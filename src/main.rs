#![feature(assert_matches)]

mod common;
mod context;
mod name_resolution;
mod parser;
mod types;
mod utils;
mod visitors;

use crate::context::GlobalCtx;
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::AluminaVisitor;
use crate::visitors::pass1::FirstPassVisitor;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
// const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

fn main() {
    let global_ctx = GlobalCtx::new();

    let parsed = parser::parse(SOURCE_CODE);
    let root_node = parsed.root_node();
    println!("{:#?}", utils::NodeWrapper::new(SOURCE_CODE, root_node));

    let root_scope = Scope::new();
    let module_scope = root_scope.make_child(ScopeType::Crate, "hello_world");
    root_scope
        .add_item("hello_world", Item::Module(module_scope.clone()))
        .unwrap();

    let mut visitor = FirstPassVisitor::new(&global_ctx, SOURCE_CODE, module_scope);
    visitor.visit(root_node).unwrap();

    println!("{:#?}", root_scope);
}
