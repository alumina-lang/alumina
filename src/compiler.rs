use std::collections::HashMap;
use std::path::PathBuf;

use colored::Colorize;

use crate::codegen;
use crate::common::AluminaError;
use crate::common::Marker;
use crate::ir::mono::MonoCtx;
use crate::ir::mono::Monomorphizer;
use crate::ir::IrCtx;

use crate::ast::maker::AstItemMaker;
use crate::ast::AstCtx;

use crate::common::CodeErrorBuilder;
use crate::common::FileId;
use crate::name_resolution::pass1::FirstPassVisitor;
use crate::name_resolution::scope::Scope;
use crate::parser::{AluminaVisitor, ParseCtx};

pub struct Compiler {
    file_map: HashMap<FileId, SourceFile>,
}

pub struct SourceFile {
    pub filename: PathBuf,
    pub path: String,
}

impl Compiler {
    pub fn new(source_files: Vec<SourceFile>) -> Self {
        let mut file_map = HashMap::new();
        for source_file in source_files {
            let id = FileId { id: file_map.len() };
            file_map.insert(id, source_file);
        }

        Self { file_map }
    }

    fn compile_inner(&mut self) -> Result<String, AluminaError> {
        let ast = AstCtx::new();
        let root_scope = Scope::new_root();

        let source_files: Vec<_> = self
            .file_map
            .iter()
            .map(|(file_id, source_file)| {
                let source = std::fs::read_to_string(&source_file.filename)?;
                let parse_tree = ParseCtx::from_source(*file_id, source);
                Ok((parse_tree, ast.parse_path(&source_file.path)))
            })
            .collect::<Result<_, AluminaError>>()?;

        for (ctx, path) in &source_files {
            let scope = root_scope.ensure_module(path.clone()).with_no_span()?;
            scope.set_code(ctx);

            let mut visitor = FirstPassVisitor::new(&ast, scope.clone());
            visitor.visit(ctx.root_node())?;
        }

        let mut item_maker = AstItemMaker::new(&ast);
        item_maker.make(root_scope)?;

        drop(source_files);

        let ir_ctx = IrCtx::new();
        let (items, lang_items) = item_maker.into_inner();
        let mut mono_ctx = MonoCtx::new(&ir_ctx, lang_items);

        for item in items {
            let inner = item.get();

            // Alumina will tree-shake and only emit the items that are actually used.
            // The functions that are marked with export will always be emitted, otherwise
            // only the functions that are transitively called from the entry point will be
            // emitted.
            if inner.should_compile() {
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx);
                monomorphizer.monomorphize(item)?;
            }
        }
        let items = mono_ctx.into_inner();

        // Dunno why the borrow checker is not letting me do that, it should be possible.
        // drop(ast);

        Ok(codegen::codegen(&items[..])?)
    }

    pub fn compile(&mut self) -> Result<String, AluminaError> {
        self.compile_inner()
    }

    fn line_and_column(&self, filename: &std::path::Path, byte_offset: usize) -> (usize, usize) {
        let source = std::fs::read_to_string(filename).unwrap();
        let mut line = 1;
        let mut column = 1;
        for (i, c) in source.chars().enumerate() {
            if i == byte_offset {
                break;
            }
            if c == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        (line, column)
    }

    pub fn print_error_report(&self, error: AluminaError) -> Result<(), AluminaError> {
        let code_errors = match error {
            AluminaError::CodeErrors(errors) => errors,
            _ => return Err(error),
        };

        for error in code_errors {
            let tagline = format!("{}: {}", "error".red(), error.kind.to_string()).bold();
            eprintln!("{}", tagline);

            // An error can happen deep inside the code that we didn't write because most of the typechecking
            // happens during or after monomorphization.
            let mut skip = false;
            for frame in error.backtrace {
                let span = match (frame, skip) {
                    (Marker::Span(span), false) => {
                        skip = true;
                        span
                    }
                    (Marker::Span(_), true) => continue,
                    (Marker::Monomorphization, _) => {
                        skip = false;
                        continue;
                    }
                };

                let file = self.file_map.get(&span.file).unwrap();
                let (line, column) = self.line_and_column(&file.filename, span.start);
                eprintln!(" --> {}:{}:{}", file.filename.display(), line, column,);
            }

            eprintln!();
        }

        Ok(())
    }
}
