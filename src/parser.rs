use std::{marker::PhantomData, rc::Rc};

use crate::{
    ast::{Expr, ExprP, NodeId, SymbolP, Ty, TyP},
    context::{GlobalCtx, Incrementable},
};

include!(concat!(env!("OUT_DIR"), "/parser.rs"));

struct ParseCtxInner<'gcx, 'src> {
    global_ctx: &'gcx GlobalCtx<'gcx>,
    // filename: &'src str,
    pub source: &'src str,
    tree: tree_sitter::Tree,
}

#[derive(Clone)]
pub struct ParseCtx<'gcx, 'src>(Rc<ParseCtxInner<'gcx, 'src>>);

impl<'gcx, 'src> ParseCtx<'gcx, 'src> {
    pub fn from_source(global_ctx: &'gcx GlobalCtx<'gcx>, source: &'src str) -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(language()).unwrap();

        let tree = parser.parse(source, None).unwrap();

        let inner = ParseCtxInner {
            global_ctx,
            source,
            tree,
        };

        ParseCtx(Rc::new(inner))
    }

    pub fn source(&self) -> &'src str {
        self.0.source
    }

    pub fn root_node(&'src self) -> tree_sitter::Node<'src> {
        self.0.tree.root_node()
    }

    pub fn make_id(&self) -> NodeId {
        self.0.global_ctx.make_id()
    }

    pub fn make_symbol<T: AsRef<str>>(&self, debug_name: Option<T>) -> SymbolP<'gcx> {
        self.0.global_ctx.make_symbol(debug_name)
    }

    pub fn intern_type(&self, ty: Ty<'gcx>) -> TyP<'gcx> {
        self.0.global_ctx.intern_type(ty)
    }

    pub fn alloc_expr(&self, expr: Expr<'gcx>) -> ExprP<'gcx> {
        self.0.global_ctx.arena.alloc(expr)
    }

    pub fn alloc_str(&self, slice: &'_ str) -> &'gcx str {
        self.0.global_ctx.arena.alloc_str(slice)
    }

    pub fn alloc_slice<T: Copy>(&self, slice: &'_ [T]) -> &'gcx [T] {
        self.0.global_ctx.arena.alloc_slice_copy(slice)
    }

    pub fn alloc_range<I, T>(&self, iter: I) -> &'gcx [T]
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        self.0.global_ctx.arena.alloc_slice_fill_iter(iter)
    }

    pub fn node_text(&self, node: tree_sitter::Node<'src>) -> &'src str {
        &self.0.source[node.byte_range()]
    }
}
