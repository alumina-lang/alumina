use crate::ast::{AstId, ItemCell, ItemP, Ty, TyP};
use crate::common::{Allocatable, ArenaAllocatable};

use crate::utils::Incrementable;
use bumpalo::Bump;
use once_cell::unsync::OnceCell;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;

pub struct AstCtx<'ast> {
    pub arena: Bump,
    pub counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'ast>>>,
}

impl<'ast> AstCtx<'ast> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::new()),
        }
    }

    pub fn make_id(&self) -> AstId {
        AstId {
            id: self.counter.increment(),
        }
    }

    pub fn intern_type(&'ast self, ty: Ty<'ast>) -> TyP<'ast> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return *key;
        }

        let inner = self.arena.alloc(ty);
        self.types.borrow_mut().insert(inner);

        inner
    }

    pub fn make_symbol<T: AsRef<str>>(&'ast self, debug_name: Option<T>) -> ItemP<'ast> {
        let debug_name = debug_name.map(|v| self.arena.alloc_str(v.as_ref()) as &str);
        let inner = self.arena.alloc(ItemCell {
            id: self.make_id(),
            debug_name,
            contents: OnceCell::new(),
        });

        inner
    }
}

impl<T: Allocatable> Allocatable for &'_ T {}

impl<'gcx, T: Allocatable> ArenaAllocatable<'gcx, AstCtx<'gcx>> for T
where
    T: 'gcx,
{
    type ReturnType = &'gcx T;

    fn alloc_on(self, ctx: &'gcx AstCtx<'gcx>) -> Self::ReturnType {
        ctx.arena.alloc(self)
    }
}

impl<'gcx, T: Allocatable + Copy> ArenaAllocatable<'gcx, AstCtx<'gcx>> for &'_ [T]
where
    T: 'gcx,
{
    type ReturnType = &'gcx [T];

    fn alloc_on(self, ctx: &'gcx AstCtx<'gcx>) -> Self::ReturnType {
        ctx.arena.alloc_slice_copy(self)
    }
}

impl<'gcx> ArenaAllocatable<'gcx, AstCtx<'gcx>> for &str {
    type ReturnType = &'gcx str;

    fn alloc_on(self, ctx: &'gcx AstCtx<'gcx>) -> Self::ReturnType {
        ctx.arena.alloc_str(self)
    }
}

impl<'gcx, T: Allocatable> ArenaAllocatable<'gcx, AstCtx<'gcx>> for Vec<T>
where
    T: 'gcx,
{
    type ReturnType = &'gcx [T];

    fn alloc_on(self, ctx: &'gcx AstCtx<'gcx>) -> Self::ReturnType {
        ctx.arena.alloc_slice_fill_iter(self)
    }
}
