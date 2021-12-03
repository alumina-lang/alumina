mod mono;

use crate::{
    ast::{BinOp, BuiltinType, Lit, UnOp},
    common::impl_allocatable,
};
use std::{
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
};

use once_cell::unsync::OnceCell;

#[derive(PartialEq, Copy, Clone, Eq, Hash)]
pub struct IrId {
    pub id: usize,
}

impl Display for IrId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.id)
    }
}

impl Debug for IrId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ty<'ir> {
    Extern(IrId),
    NamedType(IRItemP<'ir>),
    Builtin(BuiltinType),
    Pointer(TyP<'ir>),
    Array(TyP<'ir>, usize),
    Slice(TyP<'ir>),
    Tuple(&'ir [TyP<'ir>]),
    Function(&'ir [TyP<'ir>], TyP<'ir>),
}

pub type TyP<'ir> = &'ir Ty<'ir>;

#[derive(Debug, Clone, Copy)]
pub struct Field<'ir> {
    pub name: &'ir str,
    pub ty: TyP<'ir>,
}

#[derive(Debug)]
pub struct Struct<'ir> {
    pub fields: &'ir [Field<'ir>],
}

#[derive(Debug, Clone, Copy)]
pub struct Parameter<'ir> {
    pub id: IrId,
    pub ty: TyP<'ir>,
}

#[derive(Debug)]
pub struct Function<'ir> {
    pub parameters: &'ir [Parameter<'ir>],
    pub return_type: TyP<'ir>,
    pub body: ExprP<'ir>,
}

#[derive(Debug)]
pub enum IRItem<'ir> {
    Struct(Struct<'ir>),
    Function(Function<'ir>),
}

pub type IRItemP<'ir> = &'ir IRItemCell<'ir>;

impl<'ir> IRItemCell<'ir> {
    pub fn assign(&self, value: IRItem<'ir>) {
        self.contents.set(value).unwrap();
    }
    pub fn get(&'ir self) -> &'ir IRItem<'ir> {
        self.contents.get().unwrap()
    }
}
pub struct IRItemCell<'ir> {
    pub id: IrId,
    pub debug_name: Option<&'ir str>,
    pub contents: OnceCell<IRItem<'ir>>,
}

impl Hash for IRItemCell<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Symbols have reference semantics. Two structs with the same fields
/// are not considered equal.
impl PartialEq for IRItemCell<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for IRItemCell<'_> {}

impl Debug for IRItemCell<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let debug_name = self.debug_name.unwrap_or("<unnamed>");

        if fmt.alternate() {
            writeln!(fmt, "{} ({}) {{", self.id, debug_name)?;
            writeln!(fmt, "\t{:?}", self.contents.get())?;
            writeln!(fmt, "}}")?;
        } else {
            write!(fmt, "{} ({})", self.id, debug_name)?
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Statement<'ir> {
    Expression(ExprP<'ir>),
    LocalDef(IrId, TyP<'ir>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprKind<'ir> {
    Block(&'ir [Statement<'ir>], ExprP<'ir>),
    Binary(ExprP<'ir>, BinOp, ExprP<'ir>),
    Call(ExprP<'ir>, &'ir [ExprP<'ir>]),
    Function(IRItemP<'ir>),
    Ref(ExprP<'ir>),
    Deref(ExprP<'ir>),
    Unary(UnOp, ExprP<'ir>),
    Assign(ExprP<'ir>, ExprP<'ir>),
    AssignOp(BinOp, ExprP<'ir>, ExprP<'ir>),
    Local(IrId),
    Lit(Lit<'ir>),
    Tuple(&'ir [ExprP<'ir>]),
    Field(ExprP<'ir>, &'ir str),
    TupleIndex(ExprP<'ir>, usize),
    If(ExprP<'ir>, ExprP<'ir>, ExprP<'ir>),
    Cast(ExprP<'ir>, TyP<'ir>),
    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ValueType {
    LValue,
    RValue,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Expr<'ir> {
    pub kind: ExprKind<'ir>,
    pub value_type: ValueType,
    pub typ: TyP<'ir>,
}

pub type ExprP<'ir> = &'ir Expr<'ir>;

impl_allocatable!(Expr<'_>, Ty<'_>);
