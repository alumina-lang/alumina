pub mod builder;
pub mod const_eval;
pub mod infer;
pub mod lang;
pub mod mono;
pub mod optimize;

use crate::{
    ast::{Attribute, BinOp, BuiltinType, UnOp},
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
    Pointer(TyP<'ir>, bool),
    Array(TyP<'ir>, usize),
    Tuple(&'ir [TyP<'ir>]),
    Fn(&'ir [TyP<'ir>], TyP<'ir>),
}

impl<'ir> Ty<'ir> {
    pub fn assignable_from(&self, other: &Ty<'ir>) -> bool {
        match (self, other) {
            _ if self == other => true,
            (Ty::Pointer(a, true), Ty::Pointer(b, _)) if a == b => true,
            (_, Ty::Builtin(BuiltinType::Never)) => true,
            _ => false,
        }
    }

    pub fn gcd(lhs: &Ty<'ir>, rhs: &Ty<'ir>) -> Ty<'ir> {
        match (lhs, rhs) {
            _ if lhs == rhs => *lhs,
            (Ty::Pointer(a, false), Ty::Pointer(b, _)) if a == b => Ty::Pointer(a, false),
            (Ty::Pointer(a, _), Ty::Pointer(b, false)) if a == b => Ty::Pointer(a, false),

            (_, Ty::Builtin(BuiltinType::Never)) => *lhs,
            (Ty::Builtin(BuiltinType::Never), _) => *rhs,

            _ => Ty::Builtin(BuiltinType::Void),
        }
    }

    pub fn canonical_type(&'ir self) -> TyP<'ir> {
        match self {
            Ty::Pointer(inner, _) => inner.canonical_type(),
            _ => self,
        }
    }

    pub fn is_void(&self) -> bool {
        match self {
            Ty::Builtin(BuiltinType::Void) => true,
            _ => false,
        }
    }
}

pub type TyP<'ir> = &'ir Ty<'ir>;

#[derive(Debug, Clone, Copy)]
pub struct Field<'ir> {
    pub id: IrId,
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
pub struct FuncBodyCell<'ir> {
    contents: OnceCell<&'ir [Statement<'ir>]>,
}

impl<'ir> FuncBodyCell<'ir> {
    pub fn new() -> Self {
        Self {
            contents: OnceCell::new(),
        }
    }

    pub fn assign(&self, value: &'ir [Statement<'ir>]) {
        self.contents.set(value).unwrap();
    }
    pub fn get(&'ir self) -> &'ir [Statement<'ir>] {
        self.contents.get().unwrap()
    }

    pub fn is_empty(&self) -> bool {
        self.contents.get().is_none()
    }
}

#[derive(Debug)]
pub struct Function<'ir> {
    pub name: Option<&'ir str>,
    pub attributes: &'ir [Attribute],
    pub args: &'ir [Parameter<'ir>],
    pub return_type: TyP<'ir>,
    pub body: FuncBodyCell<'ir>,
}

#[derive(Debug)]
pub struct EnumMember<'ir> {
    pub id: IrId,
    pub value: ExprP<'ir>,
}

#[derive(Debug)]
pub struct Enum<'ir> {
    pub underlying_type: TyP<'ir>,
    pub members: &'ir [EnumMember<'ir>],
}

#[derive(Debug)]
pub enum IRItem<'ir> {
    Struct(Struct<'ir>),
    Function(Function<'ir>),
    Enum(Enum<'ir>),
}

pub type IRItemP<'ir> = &'ir IRItemCell<'ir>;

impl<'ir> IRItemCell<'ir> {
    pub fn assign(&self, value: IRItem<'ir>) {
        // Panic if we try to assign the same symbol twice
        self.contents
            .set(value)
            .expect("assigning the same symbol twice");
    }

    pub fn try_get(&'ir self) -> Option<&'ir IRItem<'ir>> {
        self.contents.get()
    }

    pub fn get(&'ir self) -> &'ir IRItem<'ir> {
        self.contents.get().unwrap()
    }

    pub fn get_function(&'ir self) -> &'ir Function<'ir> {
        match self.contents.get() {
            Some(IRItem::Function(f)) => f,
            _ => panic!("function expected"),
        }
    }

    pub fn get_struct(&'ir self) -> &'ir Struct<'ir> {
        match self.contents.get() {
            Some(IRItem::Struct(s)) => s,
            _ => panic!("struct expected"),
        }
    }

    pub fn get_enum(&'ir self) -> &'ir Enum<'ir> {
        match self.contents.get() {
            Some(IRItem::Enum(e)) => e,
            _ => panic!("enum expected"),
        }
    }
}
pub struct IRItemCell<'ir> {
    pub id: IrId,
    contents: OnceCell<IRItem<'ir>>,
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
    Label(IrId),
}

impl<'ir> Statement<'ir> {
    pub fn pure(&self) -> bool {
        match self {
            Statement::Expression(expr) => expr.pure(),
            Statement::LocalDef(_, _) => false,
            Statement::Label(_) => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Lit<'ast> {
    Str(&'ast [u8]),
    Int(u128),
    Float(&'ast str),
    Bool(bool),
    Null,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprKind<'ir> {
    Block(&'ir [Statement<'ir>], ExprP<'ir>),
    Binary(BinOp, ExprP<'ir>, ExprP<'ir>),
    AssignOp(BinOp, ExprP<'ir>, ExprP<'ir>),
    Call(ExprP<'ir>, &'ir [ExprP<'ir>]),
    Fn(IRItemP<'ir>),
    Ref(ExprP<'ir>),
    Deref(ExprP<'ir>),
    Return(ExprP<'ir>),
    Goto(IrId),
    Unary(UnOp, ExprP<'ir>),
    Assign(ExprP<'ir>, ExprP<'ir>),
    Index(ExprP<'ir>, ExprP<'ir>),
    Local(IrId),
    Lit(Lit<'ir>),
    ConstValue(const_eval::Value),
    Field(ExprP<'ir>, IrId),
    TupleIndex(ExprP<'ir>, usize),
    If(ExprP<'ir>, ExprP<'ir>, ExprP<'ir>),
    Cast(ExprP<'ir>),
    Unreachable,
    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub enum ValueType {
    LValue,
    RValue,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Expr<'ir> {
    pub value_type: ValueType,
    pub is_const: bool,
    pub kind: ExprKind<'ir>,
    pub ty: TyP<'ir>,
}

impl<'ir> Expr<'ir> {
    pub fn lvalue(kind: ExprKind<'ir>, typ: TyP<'ir>) -> Self {
        Self {
            kind,
            value_type: ValueType::LValue,
            is_const: false,
            ty: typ,
        }
    }

    pub fn rvalue(kind: ExprKind<'ir>, typ: TyP<'ir>) -> Self {
        Self {
            kind,
            value_type: ValueType::RValue,
            is_const: false,
            ty: typ,
        }
    }

    pub fn const_lvalue(kind: ExprKind<'ir>, typ: TyP<'ir>) -> Self {
        Self {
            kind,
            value_type: ValueType::LValue,
            is_const: true,
            ty: typ,
        }
    }

    pub fn diverges(&self) -> bool {
        *self.ty == Ty::Builtin(BuiltinType::Never)
    }

    pub fn is_void(&self) -> bool {
        match self.kind {
            ExprKind::Void => true,
            _ => false,
        }
    }

    pub fn is_unreachable(&self) -> bool {
        match self.kind {
            ExprKind::Unreachable => true,
            _ => false,
        }
    }

    pub fn pure(&self) -> bool {
        match self.kind {
            ExprKind::Block(stmts, e) => stmts.iter().all(|s| s.pure()) && e.pure(),
            ExprKind::Binary(_, a, b) => a.pure() && b.pure(),
            ExprKind::Ref(inner) => inner.pure(),
            ExprKind::Deref(inner) => inner.pure(),
            ExprKind::Unary(_, inner) => inner.pure(),
            ExprKind::Index(a, b) => a.pure() && b.pure(),
            ExprKind::If(a, b, c) => a.pure() && b.pure() && c.pure(),
            ExprKind::Cast(inner) => inner.pure(),
            ExprKind::Field(inner, _) => inner.pure(),
            ExprKind::TupleIndex(inner, _) => inner.pure(),

            ExprKind::Fn(_) => true,
            ExprKind::Local(_) => true,
            ExprKind::Lit(_) => true,
            ExprKind::ConstValue(_) => true,
            ExprKind::Void => true,

            ExprKind::Unreachable => false, // ?
            ExprKind::Call(_, _) => false,  // for now
            ExprKind::Assign(_, _) => false,
            ExprKind::AssignOp(_, _, _) => false,
            ExprKind::Return(_) => false,
            ExprKind::Goto(_) => false,
        }
    }
}

pub type ExprP<'ir> = &'ir Expr<'ir>;

impl_allocatable!(
    Expr<'_>,
    Ty<'_>,
    Statement<'_>,
    Field<'_>,
    Parameter<'_>,
    IRItemCell<'_>,
    EnumMember<'_>,
    IrId
);
