#![feature(assert_matches)]

mod ast;
mod codegen;
mod common;
mod ir;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use ast::Item;
use ir::mono::MonoCtx;
use ir::mono::Monomorphizer;
use ir::IrCtx;

use crate::ast::maker::Maker;
use crate::ast::AstCtx;
use crate::ast::Function;
use crate::name_resolution::scope::{NamedItem, Scope, ScopeType};
use crate::parser::{AluminaVisitor, ParseCtx};
use crate::utils::NodeWrapper;
use crate::visitors::pass1::FirstPassVisitor;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
// const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

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
        println!("{:?}", NodeWrapper::new(ctx.source(), ctx.root_node()));

        let module_scope =
            crate_scope.named_child_with_ctx(ScopeType::Module, &units[i].name, ctx.clone());

        crate_scope
            .add_item(&units[i].name, NamedItem::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(&ast, module_scope.clone());
        visitor.visit(ctx.root_node()).unwrap();
    }

    let mut maker = Maker::new(&ast);
    maker.make(crate_scope).unwrap();

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

    let last = match maker.symbols.last().unwrap().contents.get().unwrap() {
        Item::Function(Function { return_type, .. }) => return_type,
        _ => unreachable!(),
    };

    let ir_ctx = IrCtx::new();

    let mut mono_ctx = MonoCtx::new(&ir_ctx);
    let mut monomorphizer = Monomorphizer::new(&mut mono_ctx);

    monomorphizer.monomorphize_type(last).unwrap();
    let items = mono_ctx.into_inner();

    //drop(ast);

    println!("{:#?}", items);
}

fn main() {
    compile(vec![CompilationUnit {
        source: SOURCE_CODE.to_string(),
        name: "m".to_string(),
    }]);
}
