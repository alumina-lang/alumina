use std::{
    borrow::Borrow,
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
    StructOrEnum(SymbolP<'tcx>),
    Builtin(BuiltinType),
    Pointer(TyP<'tcx>),
    Array(TyP<'tcx>, usize),
    Slice(TyP<'tcx>),
    Tuple(&'tcx [TyP<'tcx>]),
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

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct SymbolP<'tcx> {
    id: usize,
    _phantom: PhantomData<&'tcx ()>,
}

impl SymbolP<'_> {
    pub fn new(id: usize) -> Self {
        SymbolP {
            id,
            _phantom: PhantomData,
        }
    }
}

impl Debug for SymbolP<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "SymbolP({})", self.id)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Field<'tcx> {
    name: String,
    ty: Ty<'tcx>,
}

struct Struct<'tcx> {
    fields: Vec<Field<'tcx>>,
}
