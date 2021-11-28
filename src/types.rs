use std::hash::{Hash, Hasher};
use std::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    fmt::{Debug, Formatter},
    marker::PhantomData,
};

#[derive(Debug, PartialEq, Copy, Clone, Eq, Hash)]
pub enum BuiltinType {
    Void,
    Never,
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    USize,
    ISize,
    I8,
    I16,
    I32,
    I64,
    I128,
    F32,
    F64,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ty<'tcx> {
    Placeholder(SymbolP<'tcx>),
    NamedType(SymbolP<'tcx>),
    Builtin(BuiltinType),
    Pointer(TyP<'tcx>),
    Array(TyP<'tcx>, usize),
    Slice(TyP<'tcx>),
    Tuple(&'tcx [TyP<'tcx>]),
    Function(&'tcx [TyP<'tcx>], TyP<'tcx>),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct TyP<'tcx> {
    inner: &'tcx Ty<'tcx>,
}

impl<'tcx> TyP<'tcx> {
    pub fn new(inner: &'tcx Ty<'tcx>) -> Self {
        TyP { inner }
    }
}

impl<'tcx> Borrow<Ty<'tcx>> for TyP<'tcx> {
    fn borrow(&self) -> &'_ Ty<'tcx> {
        self.inner
    }
}

pub enum Symbol<'tcx> {
    Struct(Struct<'tcx>),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct SymbolP<'tcx> {
    inner: &'tcx SymbolInner<'tcx>,
}

impl<'tcx> SymbolP<'tcx> {
    pub fn new(inner: &'tcx SymbolInner<'tcx>) -> Self {
        SymbolP { inner }
    }
}

pub struct SymbolInner<'tcx> {
    pub id: usize,
    pub contents: RefCell<Option<Symbol<'tcx>>>,
}

impl Hash for SymbolInner<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl PartialEq for SymbolInner<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for SymbolInner<'_> {}

impl Debug for SymbolInner<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "Symbol({})", self.id)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Field<'tcx> {
    name: String,
    ty: Ty<'tcx>,
}

pub struct Struct<'tcx> {
    fields: Vec<Field<'tcx>>,
}
