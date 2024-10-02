use crate::ast::maker::AstItemMaker;
use crate::ast::serialization::{AstLoader, AstSaver};
use crate::ast::{AstCtx, MacroCtx};
use crate::codegen;
use crate::common::{AluminaError, ArenaAllocatable, CodeDiagnostic, CodeErrorBuilder, HashSet};

use crate::global_ctx::GlobalCtx;
use crate::ir::dce::DeadCodeEliminator;
use crate::ir::mono::{Mono, MonoCtx};
use crate::ir::IrCtx;
use crate::parser::{AluminaVisitor, ParseCtx};
use crate::src::pass1::FirstPassVisitor;
use crate::src::scope::{Scope, ScopeType};

use std::io::{Read, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

// AST serialization is very tightly coupled to the compiler, so if anything changes,
// we invalidate the version (preventing an incompatible AST from being loaded). This is
// currently based on the compound hash of all the source files, but it could be changed to
// git revision or something else.
const VERSION_STRING: &[u8] = alumina_boot_macros::sources_hash!();

#[derive(Debug, Clone)]
pub enum Stage {
    Init,
    Parse,
    Pass1,
    Ast,
    Serialize,
    Deserialize,
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

    /// Main compile sequence. Takes a list of Alumina source files and compiles them into a single
    /// C source file.
    pub fn compile(
        &mut self,
        precompiled: Vec<PathBuf>,
        source_files: Vec<SourceFile>,
        start_time: Instant,
    ) -> Result<Option<String>, AluminaError> {
        let mut cur_time = start_time;
        timing!(self, cur_time, Stage::Init);

        let ast = AstCtx::new();
        let root_scope = Scope::new_root();

        if !precompiled.is_empty() {
            let mut loader = AstLoader::new(self.global_ctx.clone(), &ast, VERSION_STRING);

            for precompiled_file in precompiled {
                let reader = std::fs::File::open(precompiled_file)?;
                let mut buf_reader = std::io::BufReader::new(reader);

                loader.load(buf_reader.by_ref(), root_scope.clone())?;
            }
            timing!(self, cur_time, Stage::Deserialize);
        }

        let source_files: Vec<_> = source_files
            .iter()
            .map(|source_file| {
                let diag = self.global_ctx.diag();

                let file_id = diag.make_file_id();
                diag.add_file(file_id, source_file.filename.clone());

                let source = std::fs::read_to_string(&source_file.filename)?;
                let parse_tree = ParseCtx::from_source(file_id, source);
                parse_tree.check_syntax_errors(parse_tree.root_node())?;

                Ok((parse_tree, ast.parse_path(&source_file.path)))
            })
            .collect::<Result<_, AluminaError>>()?;

        timing!(self, cur_time, Stage::Parse);

        for (ctx, path) in source_files.iter() {
            let scope = root_scope
                .ensure_module(
                    path.clone(),
                    if path.is_root() {
                        ScopeType::Root
                    } else {
                        ScopeType::Module
                    },
                )
                .with_no_span()?;
            scope.set_code(ctx);

            if self.global_ctx.should_generate_main_glue() {
                let mut visitor = FirstPassVisitor::with_main(
                    self.global_ctx.clone(),
                    &ast,
                    scope,
                    MacroCtx::default(),
                );
                visitor.visit(ctx.root_node())?;
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
        item_maker.make(root_scope.clone())?;

        timing!(self, cur_time, Stage::Ast);

        if let Some(filename) = self.global_ctx.option("dump-ast") {
            let writer: Box<dyn Write> = if let Some(filename) = filename {
                Box::new(std::fs::File::create(filename)?)
            } else {
                Box::new(std::io::stdout())
            };

            let mut writer = std::io::BufWriter::new(writer);
            let mut saver = AstSaver::new(self.global_ctx.clone(), &ast, VERSION_STRING);
            saver.add_scope(&root_scope)?;
            saver.save(writer.by_ref())?;

            writer.flush()?;
            timing!(self, cur_time, Stage::Serialize);
        }

        if self.global_ctx.has_option("ast-only") {
            return Ok(None);
        }

        let mut items = HashSet::default();
        root_scope.collect_items(&mut items);

        let ir_ctx = IrCtx::new();
        drop(source_files);

        let mut mono_ctx = MonoCtx::new(&ast, &ir_ctx, self.global_ctx.clone());

        let mut roots = HashSet::default();

        let mut test_main_candidates = Vec::new();
        let mut main_candidates = Vec::new();

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

            if self.global_ctx.should_generate_main_glue() && inner.is_main_candidate() {
                if inner.is_test_main_candidate() {
                    test_main_candidates.push(item);
                } else {
                    main_candidates.push(item);
                }
            }

            if compile {
                let mut monomorphizer = Mono::new(&mut mono_ctx, false, None);
                roots.insert(monomorphizer.mono_item(item, &[])?);
            }
        }

        // Main glue code
        if self.global_ctx.should_generate_main_glue() {
            let main_candidate = if test_main_candidates.len() > 1 {
                return Err(CodeDiagnostic::MultipleMainFunctions)
                    .with_span(test_main_candidates[1].get_function().span);
            } else if !test_main_candidates.is_empty() {
                test_main_candidates.pop()
            } else if main_candidates.len() > 1 {
                return Err(CodeDiagnostic::MultipleMainFunctions)
                    .with_span(main_candidates[1].get_function().span);
            } else {
                main_candidates.pop()
            };

            if let Some(main_candidate) = main_candidate {
                let mut monomorphizer = Mono::new(&mut mono_ctx, false, None);
                let user_main = monomorphizer.mono_item(main_candidate, &[])?;

                let glue = ast
                    .lang_item(crate::ast::lang::Lang::EntrypointGlue)
                    .with_no_span()?;
                let mut monomorphizer = Mono::new(&mut mono_ctx, false, None);

                let main_ty = ir_ctx.intern_type(crate::ir::Ty::Item(user_main));

                roots.insert(monomorphizer.mono_item(glue, [main_ty].alloc_on(&ir_ctx))?);
            }
        }

        timing!(self, cur_time, Stage::Mono);

        let mut dce = DeadCodeEliminator::new();
        for item in roots {
            dce.visit_item(item)?;
        }

        // Finally generate static initialization code
        let mut monomorphizer = Mono::new(&mut mono_ctx, false, None);
        if let Some(item) = monomorphizer.generate_static_constructor(dce.alive_items())? {
            dce.visit_item(item)?;
        }

        let items: Vec<_> = dce.alive_items().iter().copied().collect();
        timing!(self, cur_time, Stage::Optimizations);

        // Dunno why the borrow checker is not letting me do that, it should be possible.
        // drop(ast);

        let res = codegen::codegen(&ir_ctx, self.global_ctx.clone(), &items[..])?;
        timing!(self, cur_time, Stage::Codegen);

        Ok(Some(res))
    }
}
