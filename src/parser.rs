use std::{marker::PhantomData, rc::Rc};

use crate::{
    ast::AstCtx,
    ast::{AstId, Expr, ExprP, ItemP, Ty, TyP},
    common::{Allocatable, ArenaAllocatable},
};

include!(concat!(env!("OUT_DIR"), "/parser.rs"));

pub struct ParseCtx<'src> {
    pub source: &'src str,
    tree: tree_sitter::Tree,
}

impl<'src> ParseCtx<'src> {
    pub fn from_source(source: &'src str) -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(language()).unwrap();

        let tree = parser.parse(source, None).unwrap();
        let inner = ParseCtx { source, tree };

        inner
    }

    pub fn source(&self) -> &'src str {
        self.source
    }

    pub fn root_node(&'src self) -> tree_sitter::Node<'src> {
        self.tree.root_node()
    }

    pub fn node_text(&self, node: tree_sitter::Node<'src>) -> &'src str {
        &self.source[node.byte_range()]
    }
}
