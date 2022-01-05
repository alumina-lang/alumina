use std::path::PathBuf;

use crate::codegen;
use crate::common::AluminaError;

use crate::common::ArenaAllocatable;
use crate::global_ctx::GlobalCtx;
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
    global_ctx: GlobalCtx,
}

#[derive(Debug)]
pub struct SourceFile {
    pub filename: PathBuf,
    pub path: String,
}

impl Compiler {
    pub fn new(global_ctx: GlobalCtx) -> Self {
        Self { global_ctx }
    }

    pub fn compile(&mut self, source_files: Vec<SourceFile>) -> Result<String, AluminaError> {
        let ast = AstCtx::new();
        let root_scope = Scope::new_root();

        let mut main_candidate = None;
        let source_files: Vec<_> = source_files
            .iter()
            .map(|source_file| {
                let file_id = self
                    .global_ctx
                    .diag()
                    .add_file(source_file.filename.clone());
                let source = std::fs::read_to_string(&source_file.filename)?;

                let parse_tree = ParseCtx::from_source(file_id, source);
                Ok((parse_tree, ast.parse_path(&source_file.path)))
            })
            .collect::<Result<_, AluminaError>>()?;

        for (idx, (ctx, path)) in source_files.iter().enumerate() {
            let scope = root_scope.ensure_module(path.clone()).with_no_span()?;
            scope.set_code(ctx);

            ctx.check_syntax_errors(ctx.root_node())?;

            if idx == source_files.len() - 1 && self.global_ctx.should_generate_main_glue() {
                let mut visitor =
                    FirstPassVisitor::with_main(self.global_ctx.clone(), &ast, scope.clone());
                visitor.visit(ctx.root_node())?;
                main_candidate = visitor.main_candidate();
            } else {
                let mut visitor =
                    FirstPassVisitor::new(self.global_ctx.clone(), &ast, scope.clone());
                visitor.visit(ctx.root_node())?;
            }
        }

        let mut item_maker = AstItemMaker::new(&ast, self.global_ctx.clone(), false);
        item_maker.make(root_scope)?;

        drop(source_files);

        let ir_ctx = IrCtx::new();
        let items = item_maker.into_inner();
        let mut mono_ctx = MonoCtx::new(&ast, &ir_ctx, self.global_ctx.clone());

        for item in items {
            let inner = item.get();

            // Alumina will tree-shake and only emit the items that are actually used.
            // The functions that are marked with export will always be emitted, otherwise
            // only the functions that are transitively called from the entry point will be
            // emitted.
            if inner.should_compile() {
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false);
                monomorphizer.monomorphize_item(item, &[])?;
            }
        }

        // Main glue code
        if self.global_ctx.should_generate_main_glue() {
            if let Some(main_candidate) = main_candidate {
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false);
                let user_main = monomorphizer.monomorphize_item(main_candidate, &[])?;

                let glue = ast
                    .lang_item(crate::ast::lang::LangItemKind::EntrypointGlue)
                    .with_no_span()?;
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false);

                let main_ty = ir_ctx.intern_type(crate::ir::Ty::NamedFunction(user_main));

                monomorphizer.monomorphize_item(glue, [main_ty].alloc_on(&ir_ctx))?;
            }
        }

        // Finally generate static initialization code
        let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false);
        monomorphizer.generate_static_constructor()?;

        let items = mono_ctx.into_inner();

        // Dunno why the borrow checker is not letting me do that, it should be possible.
        // drop(ast);
        codegen::codegen(&items[..])
    }
}
