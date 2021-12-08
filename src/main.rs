#![feature(assert_matches)]

mod ast;
mod codegen;
mod common;
mod ir;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use std::thread;

use ast::Item;
use ir::mono::MonoCtx;
use ir::mono::Monomorphizer;
use ir::IrCtx;

use crate::ast::maker::AstItemMaker;
use crate::ast::AstCtx;
use crate::ast::Function;
use crate::ir::mono::MonomorphizeKey;
use crate::name_resolution::scope::{NamedItem, Scope, ScopeType};
use crate::parser::{AluminaVisitor, ParseCtx};
use crate::utils::NodeWrapper;
use crate::visitors::pass1::FirstPassVisitor;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
//const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

struct CompilationUnit {
    source: String,
    name: String,
}

fn compile(units: Vec<CompilationUnit>) {
    let ast = AstCtx::new();

    let root_scope = Scope::new_root();
    let crate_scope = root_scope.named_child(ScopeType::Crate, "my_crate");

    root_scope
        .add_item("my_crate", NamedItem::Module(crate_scope.clone()))
        .unwrap();

    let parse_contexts: Vec<_> = units
        .iter()
        .map(|unit| ParseCtx::from_source(&unit.source))
        .collect();

    for (i, ctx) in parse_contexts.iter().enumerate() {
        //println!("{:?}", NodeWrapper::new(ctx.source(), ctx.root_node()));

        let module_scope =
            crate_scope.named_child_with_ctx(ScopeType::Module, &units[i].name, ctx.clone());

        crate_scope
            .add_item(&units[i].name, NamedItem::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(&ast, module_scope.clone());
        visitor.visit(ctx.root_node()).unwrap();
    }

    let mut maker = AstItemMaker::new(&ast);
    maker.make(crate_scope).unwrap();

    let items = maker.into_inner();

    // To demonstrate we don't need the source code anymore
    drop(parse_contexts);

    /*
    println!("{:#?}", maker.symbols);

    println!(
        "{:#?}",
        match maker.symbols.last().unwrap().contents.get().unwrap() {
            Item::Function(Function { body, .. }) => body,
            _ => unreachable!(),
        }
    );
    */

    let ir_ctx = IrCtx::new();
    let mut mono_ctx = MonoCtx::new(&ir_ctx);

    for item in items {
        // println!("{:#?}", item);

        let inner = item.get();
        if !inner.is_generic() {
            let mut monomorphizer = Monomorphizer::new(&mut mono_ctx);

            monomorphizer.monomorphize(item).unwrap();
        }
    }

    let items = mono_ctx.into_inner();

    //drop(ast);

    let mut codegen = codegen::CCodegen::new();
    for item in items {
        codegen.write_item(item);
    }

    println!("{}", codegen.generate());
}

fn main() {
    // Spawn thread with explicit stack size
    let child = thread::Builder::new()
        .stack_size(10000000)
        .spawn(run)
        .unwrap();

    // Wait for thread to join
    child.join().unwrap();
}

fn run() {
    compile(vec![CompilationUnit {
        source: SOURCE_CODE.to_string(),
        name: "m".to_string(),
    }]);
}
