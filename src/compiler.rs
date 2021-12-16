use std::path::PathBuf;

use crate::codegen;
use crate::common::AluminaError;

use crate::diagnostics::DiagnosticContext;
use crate::ir::mono::MonoCtx;
use crate::ir::mono::Monomorphizer;
use crate::ir::IrCtx;

use crate::ast::maker::AstItemMaker;
use crate::ast::AstCtx;

use crate::common::CodeErrorBuilder;

use crate::name_resolution::pass1::FirstPassVisitor;
use crate::name_resolution::scope::Scope;
use crate::parser::{AluminaVisitor, ParseCtx};

pub struct Compiler {
    diag_ctx: DiagnosticContext,
}

pub struct SourceFile {
    pub filename: PathBuf,
    pub path: String,
}

impl Compiler {
    pub fn new(diag_context: DiagnosticContext) -> Self {
        Self {
            diag_ctx: diag_context,
        }
    }

    pub fn compile(&mut self, source_files: Vec<SourceFile>) -> Result<String, AluminaError> {
        let ast = AstCtx::new();
        let root_scope = Scope::new_root();

        let source_files: Vec<_> = source_files
            .iter()
            .map(|source_file| {
                let file_id = self.diag_ctx.add_file(source_file.filename.clone());
                let source = std::fs::read_to_string(&source_file.filename)?;

                let parse_tree = ParseCtx::from_source(file_id, source);
                Ok((parse_tree, ast.parse_path(&source_file.path)))
            })
            .collect::<Result<_, AluminaError>>()?;

        for (ctx, path) in &source_files {
            let scope = root_scope.ensure_module(path.clone()).with_no_span()?;
            scope.set_code(ctx);

            ctx.check_syntax_errors(ctx.root_node())?;

            let mut visitor = FirstPassVisitor::new(&ast, scope.clone());
            visitor.visit(ctx.root_node())?;
        }

        let mut item_maker = AstItemMaker::new(&ast, self.diag_ctx.clone());
        item_maker.make(root_scope)?;

        drop(source_files);

        let ir_ctx = IrCtx::new();
        let (items, lang_items) = item_maker.into_inner();
        let mut mono_ctx = MonoCtx::new(&ir_ctx, self.diag_ctx.clone(), lang_items);

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

        // Finally generate static initialization code
        let mut monomorphizer = Monomorphizer::new(&mut mono_ctx);
        monomorphizer.generate_static_constructor()?;

        let items = mono_ctx.into_inner();

        // Dunno why the borrow checker is not letting me do that, it should be possible.
        // drop(ast);

        Ok(codegen::codegen(&items[..])?)
    }
}
