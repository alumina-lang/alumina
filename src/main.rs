#![feature(assert_matches)]

mod ast;
mod codegen;
mod common;
mod context;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use ast::{Struct, Symbol, SymbolP, TypedSymbol};
use common::SyntaxError;
use parser::ParseCtx;
use visitors::types::TypeVisitor;

use crate::context::GlobalCtx;
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::AluminaVisitor;
use crate::visitors::maker::Maker;
use crate::visitors::pass1::FirstPassVisitor;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
// const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

struct CompilationUnit {
    source: String,
    name: String,
}

fn compile(units: Vec<CompilationUnit>) {
    let ctx = GlobalCtx::new();

    let root_scope = Scope::new_root();
    let crate_scope = root_scope.new_child(ScopeType::Crate, "my_crate");

    root_scope
        .add_item("my_crate", Item::Module(crate_scope.clone()))
        .unwrap();

    let parse_contexts: Vec<_> = units
        .iter()
        .map(|unit| ParseCtx::from_source(&ctx, &unit.source))
        .collect();

    for (i, ctx) in parse_contexts.iter().enumerate() {
        let module_scope =
            crate_scope.new_child_with_parse_ctx(ScopeType::Module, &units[i].name, ctx.clone());

        crate_scope
            .add_item(&units[i].name, Item::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(module_scope.clone());
        visitor.visit(ctx.root_node()).unwrap();
    }

    let mut maker = Maker::new();
    maker.make(crate_scope).unwrap();

    // To demonstrate we don't need the source code anymore
    drop(parse_contexts);

    println!("{:#?}", maker.symbols);
}

fn main() {
    compile(vec![
        CompilationUnit {
            source: "struct a { inner: &mod2::a }".to_string(),
            name: "mod1".to_string(),
        },
        CompilationUnit {
            source: "struct a { inner: &mod1::a }".to_string(),
            name: "mod2".to_string(),
        },
        CompilationUnit {
            source: "struct a { inner: &mod1::a } impl a { fn foo() { 1 } }".to_string(),
            name: "mod3".to_string(),
        },
    ]);
}
