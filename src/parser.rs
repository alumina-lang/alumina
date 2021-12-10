use std::{marker::PhantomData, rc::Rc};

use once_cell::unsync::OnceCell;

use crate::{
    ast::AstCtx,
    ast::{AstId, Expr, ExprP, ItemP, Ty, TyP},
    common::{Allocatable, ArenaAllocatable},
    name_resolution::path::{Path, PathSegment},
};

include!(concat!(env!("OUT_DIR"), "/parser.rs"));

pub struct ParseCtx<'src> {
    source: String,
    tree: OnceCell<tree_sitter::Tree>,
    _phantom: PhantomData<&'src ()>,
}

impl<'src> ParseCtx<'src> {
    pub fn from_source(source: String) -> Self {
        ParseCtx {
            source,
            tree: OnceCell::new(),
            _phantom: PhantomData,
        }
    }

    pub fn source(&'src self) -> &'src str {
        &self.source
    }

    pub fn root_node(&'src self) -> tree_sitter::Node<'src> {
        match self.tree.get() {
            Some(tree) => tree.root_node(),
            None => {
                let mut parser = tree_sitter::Parser::new();
                parser.set_language(language()).unwrap();

                self.tree
                    .set(parser.parse(self.source.as_str(), None).unwrap());
                self.root_node()
            }
        }
    }

    pub fn node_text(&'src self, node: tree_sitter::Node<'src>) -> &'src str {
        &self.source[node.byte_range()]
    }
}
