use std::{marker::PhantomData, rc::Rc};

use crate::{
    ast::{AstId, Expr, ExprP, ItemP, Ty, TyP},
    common::{Allocatable, ArenaAllocatable},
    context::AstCtx,
};

include!(concat!(env!("OUT_DIR"), "/parser.rs"));

pub struct ParseCtx<'ast, 'src> {
    pub ast_ctx: &'ast AstCtx<'ast>,
    pub source: &'src str,
    tree: tree_sitter::Tree,
}

impl<'ast, 'src> ParseCtx<'ast, 'src> {
    pub fn from_source(ast_ctx: &'ast AstCtx<'ast>, source: &'src str) -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(language()).unwrap();

        let tree = parser.parse(source, None).unwrap();

        let inner = ParseCtx {
            ast_ctx,
            source,
            tree,
        };

        inner
    }

    pub fn source(&self) -> &'src str {
        self.source
    }

    pub fn root_node(&'src self) -> tree_sitter::Node<'src> {
        self.tree.root_node()
    }

    pub fn make_id(&self) -> AstId {
        self.ast_ctx.make_id()
    }

    pub fn node_text(&self, node: tree_sitter::Node<'src>) -> &'src str {
        &self.source[node.byte_range()]
    }
}
