use std::hash::{Hash, Hasher};
use std::{
    borrow::Borrow,
    fmt::{Debug, Formatter},
};

use once_cell::unsync::OnceCell;

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
pub enum Ty<'gcx> {
    Placeholder(SymbolP<'gcx>),
    NamedType(SymbolP<'gcx>),
    Builtin(BuiltinType),
    Pointer(TyP<'gcx>),
    Array(TyP<'gcx>, usize),
    Slice(TyP<'gcx>),
    Tuple(&'gcx [TyP<'gcx>]),
    Function(&'gcx [TyP<'gcx>], TyP<'gcx>),
}

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct TyP<'gcx> {
    inner: &'gcx Ty<'gcx>,
}

impl<'gcx> TyP<'gcx> {
    pub fn new(inner: &'gcx Ty<'gcx>) -> Self {
        TyP { inner }
    }
}
impl Debug for TyP<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.inner.fmt(fmt)
    }
}

impl<'gcx> Borrow<Ty<'gcx>> for TyP<'gcx> {
    fn borrow(&self) -> &'_ Ty<'gcx> {
        self.inner
    }
}

#[derive(Debug)]
pub enum Symbol<'gcx> {
    Struct(Struct<'gcx>),
    Function(Function<'gcx>),
}

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct SymbolP<'gcx> {
    pub inner: &'gcx SymbolCell<'gcx>,
}

impl<'gcx> SymbolP<'gcx> {
    pub fn new(inner: &'gcx SymbolCell<'gcx>) -> Self {
        SymbolP { inner }
    }

    pub fn assign(&self, value: Symbol<'gcx>) {
        // Panic if we try to assign the same symbol twice
        self.inner.contents.set(value).unwrap();
    }

    pub fn get(&self) -> &'gcx Symbol<'gcx> {
        self.inner.contents.get().unwrap()
    }
}

impl Debug for SymbolP<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.inner.fmt(fmt)
    }
}

/// SymbolCell is a wrapper that allows us to build recursive structures incrementally.
/// This allows us to assign symbols to syntax early in name resolution and fill them in
/// later.
/// Symbols are immutable once they are assigned.
pub struct SymbolCell<'gcx> {
    pub id: usize,
    pub debug_name: Option<&'gcx str>,
    pub contents: OnceCell<Symbol<'gcx>>,
}

impl Hash for SymbolCell<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Symbols have reference semantics. Two structs with the same fields
/// are not considered equal.
impl PartialEq for SymbolCell<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for SymbolCell<'_> {}

impl Debug for SymbolCell<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let debug_name = self.debug_name.unwrap_or("<unnamed>");

        if fmt.alternate() {
            writeln!(fmt, "{}${} {{", self.id, debug_name)?;
            writeln!(fmt, "\t{:?}", self.contents.get())?;
            writeln!(fmt, "}}")?;
        } else {
            write!(fmt, "{}${}", self.id, debug_name)?
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TypedSymbol<'gcx> {
    pub symbol: SymbolP<'gcx>,
    pub ty: TyP<'gcx>,
}

#[derive(Debug)]
pub struct Struct<'gcx> {
    pub placeholders: &'gcx [SymbolP<'gcx>],
    pub associated_fns: &'gcx [SymbolP<'gcx>],
    pub fields: &'gcx [TypedSymbol<'gcx>],
}

#[derive(Debug)]
pub struct Function<'gcx> {
    pub placeholders: &'gcx [SymbolP<'gcx>],
    pub parameters: &'gcx [TypedSymbol<'gcx>],
    pub return_type: TyP<'gcx>,
    pub body: Option<ExpressionP<'gcx>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Statement<'gcx> {
    Expression(ExpressionP<'gcx>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Expression<'gcx> {
    Block(&'gcx [Statement<'gcx>], ExpressionP<'gcx>),
    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ExpressionP<'gcx> {
    pub inner: &'gcx Expression<'gcx>,
}
