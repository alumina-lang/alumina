#![feature(backtrace)]
#![feature(assert_matches)]

mod ast;
mod codegen;
mod common;
mod ir;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use std::collections::HashMap;
use std::error::Error;
use std::path::PathBuf;

use common::AluminaError;

use ir::mono::MonoCtx;
use ir::mono::Monomorphizer;
use ir::IrCtx;

use crate::ast::maker::AstItemMaker;
use crate::ast::AstCtx;

use crate::common::FileId;
use crate::common::WithNoSpan;
use crate::name_resolution::pass1::FirstPassVisitor;
use crate::name_resolution::scope::Scope;
use crate::parser::{AluminaVisitor, ParseCtx};

struct SourceFile {
    filename: PathBuf,
    path: String,
}

fn compile(source_files: Vec<SourceFile>) -> Result<(), AluminaError> {
    let ast = AstCtx::new();
    let root_scope = Scope::new_root();

    let mut file_map: HashMap<FileId, PathBuf> = HashMap::new();
    let mut file_counter = 0;

    let source_files: Vec<_> = source_files
        .into_iter()
        .map(|source_file| {
            let source = std::fs::read_to_string(&source_file.filename)?;
            let file_id = FileId { id: file_counter };
            file_counter += 1;

            file_map.insert(file_id, source_file.filename);

            let parse_tree = ParseCtx::from_source(file_id, source);

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

    let (items, lang_items) = item_maker.into_inner();

    let ir_ctx = IrCtx::new();
    let mut mono_ctx = MonoCtx::new(&ir_ctx, lang_items);

    for item in items {
        let inner = item.get();
        if !inner.is_generic() {
            let mut monomorphizer = Monomorphizer::new(&mut mono_ctx);

            monomorphizer.monomorphize(item)?;
        }
    }

    let items = mono_ctx.into_inner();
    println!("{}", codegen::codegen(&items[..])?);

    Ok(())
}

fn main() {
    let res = compile(vec![
        SourceFile {
            filename: PathBuf::from("./stdlib/lib.alu"),
            path: "std".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./examples/minimal.alu"),
            path: "hello_world".to_string(),
        },
    ]);

    match res {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}", e);
            eprintln!("{}", e.backtrace().unwrap());
            std::process::exit(1);
        }
    }
}
