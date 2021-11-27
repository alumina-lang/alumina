use crate::types::{SymbolP, Ty, TyP};

use bumpalo::Bump;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::marker::PhantomData;

trait Incrementable<T> {
    fn increment(&self) -> T;
}

impl Incrementable<usize> for Cell<usize> {
    fn increment(&self) -> usize {
        let old = self.get();
        self.set(old + 1);
        old
    }
}

pub struct GlobalCtx<'tcx> {
    pub arena: Bump,
    counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'tcx>>>,
}

impl<'tcx> GlobalCtx<'tcx> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::new()),
        }
    }

    pub fn intern(&'tcx self, ty: Ty<'tcx>) -> TyP<'tcx> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return *key;
        }

        let inner = self.arena.alloc(ty);
        let result = TyP::new(inner);
        self.types.borrow_mut().insert(result);
        result
    }

    pub fn make_symbol(&'tcx self) -> SymbolP<'tcx> {
        SymbolP::new(self.counter.increment())
    }
}
