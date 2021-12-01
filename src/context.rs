use crate::ast::{SymbolCell, SymbolP, Ty, TyP};

use bumpalo::Bump;
use once_cell::unsync::OnceCell;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;

pub trait Incrementable<T> {
    fn increment(&self) -> T;
}

impl Incrementable<usize> for Cell<usize> {
    fn increment(&self) -> usize {
        let old = self.get();
        self.set(old + 1);
        old
    }
}

pub struct GlobalCtx<'gcx> {
    pub arena: Bump,
    pub counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'gcx>>>,
    #[cfg(test)]
    symbols: RefCell<Vec<SymbolP<'gcx>>>,
}

impl<'gcx> GlobalCtx<'gcx> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::new()),
            #[cfg(test)]
            symbols: RefCell::new(Vec::new()),
        }
    }

    pub fn intern_type(&'gcx self, ty: Ty<'gcx>) -> TyP<'gcx> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return *key;
        }

        let inner = self.arena.alloc(ty);
        let result = TyP::new(inner);
        self.types.borrow_mut().insert(result);
        result
    }

    pub fn make_symbol<T: AsRef<str>>(&'gcx self, debug_name: Option<T>) -> SymbolP<'gcx> {
        let debug_name = debug_name.map(|v| self.arena.alloc_str(v.as_ref()) as &str);

        let inner = self.arena.alloc(SymbolCell {
            id: self.counter.increment(),
            debug_name,
            contents: OnceCell::new(),
        });

        #[cfg(test)]
        self.symbols.borrow_mut().push(SymbolP::new(inner));

        SymbolP::new(inner)
    }

    #[cfg(test)]
    pub fn get_symbol(&'gcx self, id: usize) -> SymbolP<'gcx> {
        self.symbols.borrow()[id]
    }
}
