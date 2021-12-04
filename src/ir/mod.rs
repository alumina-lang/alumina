pub mod mono;

use crate::{
    ast::{BinOp, BuiltinType, Lit, UnOp},
    common::{impl_allocatable, Allocatable, ArenaAllocatable, Incrementable},
};
use std::{
    cell::{Cell, RefCell},
    collections::HashSet,
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
};

use bumpalo::Bump;
use once_cell::unsync::OnceCell;

pub struct IrCtx<'ir> {
    pub arena: Bump,
    pub counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'ir>>>,
}

impl<'ir> IrCtx<'ir> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::new()),
        }
    }

    pub fn make_id(&self) -> IrId {
        IrId {
            id: self.counter.increment(),
        }
    }

    pub fn intern_type(&'ir self, ty: Ty<'ir>) -> TyP<'ir> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return *key;
        }

        let inner = self.arena.alloc(ty);
        self.types.borrow_mut().insert(inner);

        inner
    }

    pub fn make_symbol(&'ir self) -> IRItemP<'ir> {
        let inner = self.arena.alloc(IRItemCell {
            id: self.make_id(),
            contents: OnceCell::new(),
        });

        inner
    }
}

impl<'ir, T: Allocatable> ArenaAllocatable<'ir, IrCtx<'ir>> for T
where
    T: 'ir,
{
    type ReturnType = &'ir T;

    fn alloc_on(self, ctx: &'ir IrCtx<'ir>) -> Self::ReturnType {
        ctx.arena.alloc(self)
    }
}

impl<'ir, T: Allocatable + Copy> ArenaAllocatable<'ir, IrCtx<'ir>> for &'_ [T]
where
    T: 'ir,
{
    type ReturnType = &'ir [T];

    fn alloc_on(self, ctx: &'ir IrCtx<'ir>) -> Self::ReturnType {
        ctx.arena.alloc_slice_copy(self)
    }
}

impl<'ir> ArenaAllocatable<'ir, IrCtx<'ir>> for &str {
    type ReturnType = &'ir str;

    fn alloc_on(self, ctx: &'ir IrCtx<'ir>) -> Self::ReturnType {
        ctx.arena.alloc_str(self)
    }
}

impl<'ir, T: Allocatable> ArenaAllocatable<'ir, IrCtx<'ir>> for Vec<T>
where
    T: 'ir,
{
    type ReturnType = &'ir [T];

    fn alloc_on(self, ctx: &'ir IrCtx<'ir>) -> Self::ReturnType {
        ctx.arena.alloc_slice_fill_iter(self)
    }
}

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

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
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
        if fmt.alternate() {
            writeln!(fmt, "{} {{", self.id)?;
            writeln!(fmt, "\t{:?}", self.contents.get())?;
            writeln!(fmt, "}}")?;
        } else {
            write!(fmt, "{}", self.id)?
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

impl_allocatable!(
    Expr<'_>,
    Ty<'_>,
    Statement<'_>,
    Field<'_>,
    Parameter<'_>,
    IRItemCell<'_>,
    IrId
);
