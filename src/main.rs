mod common;
mod pass1;

use common::*;
use pass1::FirstPassVisitor;
use crate::parser::AluminaVisitor;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");

pub mod parser {
    include!(concat!(env!("OUT_DIR"), "/parser.rs"));
}

fn main() {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(parser::language()).unwrap();

    let parsed = parser.parse(SOURCE_CODE, None).unwrap();
    let root_node = parsed.root_node();

    let mut root_path: Path<'_> = PathSegment::Ident("hello_world").into();
    root_path.absolute = true;

    let mut visitor = FirstPassVisitor::new(SOURCE_CODE, root_path);
    visitor.visit(root_node).unwrap();

    println!("{:#?}", visitor.root_scope);
}
