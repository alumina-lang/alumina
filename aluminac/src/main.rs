mod common;
mod pass1;

use tree_sitter_alumina::language;

use common::*;
use pass1::FirstPassVisitor;

const SOURCE_CODE: &str = include_str!("../../examples/minimal.alumina");

fn main() {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(language()).unwrap();

    let parsed = parser.parse(SOURCE_CODE, None).unwrap();
    let root_node = parsed.root_node();

    let mut root_path: Path<'_> = PathSegment::Ident("hello_world").into();
    root_path.absolute = true;

    let mut visitor = FirstPassVisitor::new(SOURCE_CODE, root_path);
    visitor.visit(root_node).unwrap();

    println!("{:#?}", visitor.root_scope);
}
