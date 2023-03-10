use crate::ast::maker::AstItemMaker;
use crate::ast::{AstCtx, MacroCtx};
use crate::codegen;
use crate::common::{AluminaError, ArenaAllocatable, CodeErrorBuilder, CodeErrorKind, HashSet};
use crate::global_ctx::GlobalCtx;
use crate::ir::dce::DeadCodeEliminator;
use crate::ir::mono::{MonoCtx, Monomorphizer};
use crate::ir::IrCtx;
use crate::name_resolution::pass1::FirstPassVisitor;
use crate::name_resolution::scope::Scope;
use crate::parser::{AluminaVisitor, ParseCtx};

use std::path::PathBuf;
use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
pub enum Stage {
    Init,
    Parse,
    Pass1,
    Ast,
    Mono,
    Optimizations,
    Codegen,
}

pub struct Compiler {
    global_ctx: GlobalCtx,
    timings: Vec<(Stage, Duration)>,
}

#[derive(Debug)]
pub struct SourceFile {
    pub filename: PathBuf,
    pub path: String,
}

macro_rules! timing {
    ($self:expr, $cur_time:expr, $stage:expr) => {
        let new_time = Instant::now();
        $self
            .timings
            .push(($stage, new_time.duration_since($cur_time)));
        #[allow(unused_assignments)]
        {
            $cur_time = new_time;
        }
    };
}

impl Compiler {
    pub fn new(global_ctx: GlobalCtx) -> Self {
        Self {
            global_ctx,
            timings: Vec::new(),
        }
    }

    pub fn timings(&self) -> impl Iterator<Item = (Stage, Duration)> + '_ {
        self.timings.iter().cloned()
    }

    pub fn compile(
        &mut self,
        source_files: Vec<SourceFile>,
        start_time: Instant,
    ) -> Result<String, AluminaError> {
        let mut cur_time = start_time;
        timing!(self, cur_time, Stage::Init);

        let ast = AstCtx::new();
        let root_scope = Scope::new_root();

        let source_files: Vec<_> = source_files
            .iter()
            .map(|source_file| {
                let file_id = self
                    .global_ctx
                    .diag()
                    .add_file(source_file.filename.clone());
                let source = std::fs::read_to_string(&source_file.filename)?;

                let parse_tree = ParseCtx::from_source(file_id, source);
                parse_tree.check_syntax_errors(parse_tree.root_node())?;

                Ok((parse_tree, ast.parse_path(&source_file.path)))
            })
            .collect::<Result<_, AluminaError>>()?;

        timing!(self, cur_time, Stage::Parse);

        let mut main_candidate = None;
        for (ctx, path) in source_files.iter() {
            let scope = root_scope.ensure_module(path.clone()).with_no_span()?;
            scope.set_code(ctx);

            if self.global_ctx.should_generate_main_glue() {
                let mut visitor = FirstPassVisitor::with_main(
                    self.global_ctx.clone(),
                    &ast,
                    scope,
                    MacroCtx::default(),
                );
                visitor.visit(ctx.root_node())?;

                if let Some(candidate) = visitor.main_candidate() {
                    if main_candidate.replace(candidate).is_some() {
                        return Err(CodeErrorKind::MultipleMainFunctions)
                            .with_span(candidate.get_function().span);
                    }
                }
            } else {
                let mut visitor = FirstPassVisitor::new(
                    self.global_ctx.clone(),
                    &ast,
                    scope,
                    MacroCtx::default(),
                );
                visitor.visit(ctx.root_node())?;
            }
        }

        timing!(self, cur_time, Stage::Pass1);

        let mut item_maker = AstItemMaker::new(&ast, self.global_ctx.clone(), MacroCtx::default());
        item_maker.make(root_scope)?;

        timing!(self, cur_time, Stage::Ast);

        drop(source_files);

        let ir_ctx = IrCtx::new();
        let items = item_maker.into_inner();
        let mut mono_ctx = MonoCtx::new(&ast, &ir_ctx, self.global_ctx.clone());

        let mut roots = HashSet::default();

        for item in items {
            let inner = item.get();

            // Alumina will tree-shake and only emit the items that are actually used.
            // The functions that are marked with export will always be emitted, otherwise
            // only the functions that are transitively called from the entry point will be
            // emitted. Can be forced to monomorphize all functions with "-Zmonomorphize-all"
            let compile = if self.global_ctx.has_option("monomorphize-all") {
                inner.can_compile()
            } else {
                inner.should_compile()
            };

            if compile {
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false, None);
                roots.insert(monomorphizer.monomorphize_item(item, &[])?);
            }
        }

        // Main glue code
        if self.global_ctx.should_generate_main_glue() {
            if let Some(main_candidate) = main_candidate {
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false, None);
                let user_main = monomorphizer.monomorphize_item(main_candidate, &[])?;

                let glue = ast
                    .lang_item(crate::ast::lang::LangItemKind::EntrypointGlue)
                    .with_no_span()?;
                let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false, None);

                let main_ty = ir_ctx.intern_type(crate::ir::Ty::Item(user_main));

                roots.insert(monomorphizer.monomorphize_item(glue, [main_ty].alloc_on(&ir_ctx))?);
            }
        }

        timing!(self, cur_time, Stage::Mono);

        let mut dce = DeadCodeEliminator::new();
        for item in roots {
            dce.visit_item(item)?;
        }

        // Finally generate static initialization code
        let mut monomorphizer = Monomorphizer::new(&mut mono_ctx, false, None);
        dce.visit_item(monomorphizer.generate_static_constructor(dce.alive_items())?)?;

        let items: Vec<_> = dce.alive_items().iter().copied().collect();
        timing!(self, cur_time, Stage::Optimizations);

        // Dunno why the borrow checker is not letting me do that, it should be possible.
        // drop(ast);

        let res = codegen::codegen(self.global_ctx.clone(), &items[..]);
        timing!(self, cur_time, Stage::Codegen);

        res
    }
}
