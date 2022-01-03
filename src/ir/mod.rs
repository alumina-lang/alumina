pub mod builder;
pub mod const_eval;
pub mod elide_zst;
pub mod infer;
pub mod lang;
pub mod mono;

use crate::{
    ast::{Attribute, BinOp, BuiltinType, UnOp},
    common::{impl_allocatable, Allocatable, ArenaAllocatable, Incrementable},
    intrinsics::CodegenIntrinsicKind,
};
use std::{
    cell::{Cell, RefCell},
    collections::HashSet,
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
};

use bumpalo::Bump;
use once_cell::unsync::OnceCell;

use self::const_eval::Value;

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
        self.arena.alloc(IRItemCell {
            id: self.make_id(),
            contents: OnceCell::new(),
        })
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
pub enum UnqualifiedKind {
    String(usize),
}

#[derive(PartialEq, Eq, Clone, Hash, Copy)]
pub enum Ty<'ir> {
    NamedType(IRItemP<'ir>),
    Protocol(IRItemP<'ir>),
    Builtin(BuiltinType),
    Pointer(TyP<'ir>, bool),
    Array(TyP<'ir>, usize),
    // TODO: Remove this when you find a better way to do it
    // Unqualified types are a bit of a hack in IR to support
    // const strings in intrinsics and other places before they
    // are coerced into a slice.
    Unqualified(UnqualifiedKind),
    Tuple(&'ir [TyP<'ir>]),
    FunctionPointer(&'ir [TyP<'ir>], TyP<'ir>),
    // Named functions are a family of unit types, each representing
    // a specific (monomorphized) function. They coerce into function
    // pointers when arg and return types match. They are proper types,
    // so they can be stored in variables, passed as arguments and as they
    // are ZSTs, all writes and reads will be elided.
    NamedFunction(IRItemP<'ir>),
}

impl Debug for Ty<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Protocol(cell) | Ty::NamedType(cell) | Ty::NamedFunction(cell) => {
                let inner = cell.try_get();
                match inner {
                    Some(IRItem::StructLike(s)) => {
                        write!(f, "{} {{ ", s.name.unwrap_or("(unnamed)"))?;
                        for field in s.fields {
                            write!(f, "{:?} ", field.ty)?;
                        }
                        write!(f, "}}")
                    }
                    Some(IRItem::Enum(e)) => {
                        write!(f, "{}", e.name.unwrap_or("(unnamed)"))
                    }
                    Some(IRItem::Protocol(s)) => {
                        write!(f, "{}", s.name.unwrap_or("(unnamed)"))
                    }
                    Some(IRItem::Function(s)) => {
                        write!(f, "{}", s.name.unwrap_or("(unnamed)"))
                    }
                    _ => write!(f, "ERROR"),
                }
            }
            Ty::Builtin(builtin) => write!(f, "{:?}", builtin),
            Ty::Pointer(ty, is_const) => {
                write!(f, "&{}{:?}", if *is_const { "" } else { "mut " }, ty)
            }
            Ty::Array(ty, len) => write!(f, "[{:?}; {}]", ty, len),
            Ty::Unqualified(kind) => write!(f, "unqualified {:?}", kind),
            Ty::Tuple(tys) => {
                write!(f, "(")?;
                for (i, ty) in tys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", ty)?;
                }
                write!(f, ")")
            }
            Ty::FunctionPointer(args, ret) => {
                write!(f, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", arg)?;
                }
                write!(f, ") -> {:?}", ret)
            }
        }
    }
}

impl<'ir> Ty<'ir> {
    /// Returns true if lhs <= rhs on the stric type hierarchy (implicit coercions are not
    /// considered).
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

    pub fn is_never(&self) -> bool {
        matches!(self, Ty::Builtin(BuiltinType::Never))
    }

    pub fn is_zero_sized(&self) -> bool {
        match self {
            Ty::Builtin(BuiltinType::Void) => true,
            Ty::Builtin(BuiltinType::Never) => true, // or false? dunno, never type is weird
            Ty::Builtin(_) => false,
            Ty::Protocol(_) => todo!(),
            Ty::NamedType(inner) => match inner.get() {
                IRItem::StructLike(s) => s.fields.iter().all(|f| f.ty.is_zero_sized()),
                IRItem::Enum(e) => e.underlying_type.is_zero_sized(),
                IRItem::Static(_) => unreachable!(),
                IRItem::Protocol(_) => unreachable!(),
                IRItem::Function(_) => unreachable!(),
                IRItem::Const(_) => unreachable!(),
            },
            Ty::Pointer(_, _) => false,
            Ty::Array(inner, size) => *size == 0 || inner.is_zero_sized(),
            Ty::Tuple(elems) => elems.iter().all(|e| e.is_zero_sized()),
            Ty::Unqualified(UnqualifiedKind::String(len)) => *len == 0,
            Ty::NamedFunction(_) => true,
            Ty::FunctionPointer(_, _) => false,
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
pub struct StructLike<'ir> {
    pub name: Option<&'ir str>,
    pub fields: &'ir [Field<'ir>],
    pub is_union: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct Parameter<'ir> {
    pub id: IrId,
    pub ty: TyP<'ir>,
}

#[derive(Debug, Copy, Clone)]
pub struct LocalDef<'ir> {
    pub id: IrId,
    pub typ: TyP<'ir>,
}

#[derive(Debug)]
pub struct FuncBody<'ir> {
    pub local_defs: &'ir [LocalDef<'ir>],
    pub statements: &'ir [Statement<'ir>],
}

#[derive(Debug)]
pub struct Function<'ir> {
    pub name: Option<&'ir str>,
    pub attributes: &'ir [Attribute],
    pub args: &'ir [Parameter<'ir>],
    pub return_type: TyP<'ir>,
    pub body: OnceCell<FuncBody<'ir>>,
}

#[derive(Debug)]
pub struct Protocol<'ir> {
    pub name: Option<&'ir str>,
    pub methods: &'ir [ProtocolFunction<'ir>],
}

#[derive(Debug)]
pub struct ProtocolFunction<'ir> {
    pub name: &'ir str,
    pub arg_types: &'ir [TyP<'ir>],
    pub return_type: TyP<'ir>,
}

#[derive(Debug)]
pub struct EnumMember<'ir> {
    pub id: IrId,
    pub value: ExprP<'ir>,
}

#[derive(Debug)]
pub struct Enum<'ir> {
    pub name: Option<&'ir str>,
    pub underlying_type: TyP<'ir>,
    pub members: &'ir [EnumMember<'ir>],
}

#[derive(Debug)]
pub struct Static<'ir> {
    pub name: Option<&'ir str>,
    pub typ: TyP<'ir>,
    pub init: Option<ExprP<'ir>>,
}

#[derive(Debug)]
pub struct Const<'ir> {
    pub name: Option<&'ir str>,
    pub value: Value<'ir>,
}

#[derive(Debug)]
pub enum IRItem<'ir> {
    StructLike(StructLike<'ir>),
    Protocol(Protocol<'ir>),
    Function(Function<'ir>),
    Enum(Enum<'ir>),
    Static(Static<'ir>),
    Const(Const<'ir>),
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
            _ => panic!("function expected: {:?}", self.contents.get()),
        }
    }

    pub fn get_protocol(&'ir self) -> &'ir Protocol<'ir> {
        match self.contents.get() {
            Some(IRItem::Protocol(p)) => p,
            _ => panic!("protocol expected"),
        }
    }

    pub fn get_struct_like(&'ir self) -> &'ir StructLike<'ir> {
        match self.contents.get() {
            Some(IRItem::StructLike(s)) => s,
            _ => panic!("struct expected"),
        }
    }

    pub fn get_static(&'ir self) -> &'ir Static<'ir> {
        match self.contents.get() {
            Some(IRItem::Static(s)) => s,
            _ => panic!("static expected"),
        }
    }

    pub fn is_struct_like(&self) -> bool {
        matches!(self.contents.get(), Some(IRItem::StructLike(_)))
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

#[derive(Debug, Clone)]
pub enum Statement<'ir> {
    Expression(ExprP<'ir>),
    Label(IrId),
}

impl<'ir> Statement<'ir> {
    pub fn pure(&self) -> bool {
        match self {
            Statement::Expression(expr) => expr.pure(),
            Statement::Label(_) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Lit<'ast> {
    Str(&'ast [u8]),
    Int(u128),
    Float(&'ast str),
    Bool(bool),
    Null,
}

#[derive(Debug, Clone)]
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
    Static(IRItemP<'ir>),
    Lit(Lit<'ir>),
    ConstValue(const_eval::Value<'ir>),
    Field(ExprP<'ir>, IrId),
    TupleIndex(ExprP<'ir>, usize),
    If(ExprP<'ir>, ExprP<'ir>, ExprP<'ir>),
    Cast(ExprP<'ir>),
    CodegenIntrinsic(CodegenIntrinsicKind<'ir>),
    Unreachable,
    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub enum ValueType {
    LValue,
    RValue,
}

#[derive(Debug, Clone)]
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
        match self.value_type {
            ValueType::LValue => false,
            ValueType::RValue => matches!(self.ty, Ty::Builtin(BuiltinType::Never)),
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self.kind, ExprKind::Void)
    }

    pub fn is_unreachable(&self) -> bool {
        matches!(self.kind, ExprKind::Unreachable)
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
            ExprKind::Static(_) => true,
            ExprKind::Lit(_) => true,
            ExprKind::ConstValue(_) => true,
            ExprKind::Void => true,

            ExprKind::CodegenIntrinsic(_) => false,
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
    ProtocolFunction<'_>,
    LocalDef<'_>,
    IrId
);
