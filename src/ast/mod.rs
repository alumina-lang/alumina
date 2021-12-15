pub mod expressions;
pub mod lang;
pub mod macros;
pub mod maker;
pub mod types;

use crate::common::{Allocatable, ArenaAllocatable, FileId, Incrementable};
use crate::intrinsics::IntrinsicKind;
use crate::name_resolution::path::{Path, PathSegment};
use std::fmt::Display;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

use bumpalo::Bump;
use once_cell::unsync::OnceCell;
use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use crate::common::impl_allocatable;

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

    pub fn make_symbol(&'ast self) -> ItemP<'ast> {
        let inner = self.arena.alloc(ItemCell {
            id: self.make_id(),
            contents: OnceCell::new(),
        });

        inner
    }

    pub fn parse_path(&'ast self, path: &'_ str) -> Path<'ast> {
        let segments: Vec<_> = path
            .split("::")
            .map(|s| PathSegment(s.alloc_on(self)))
            .collect();

        if segments[0].0.is_empty() {
            Path {
                absolute: true,
                segments: segments.into_iter().skip(1).collect(),
            }
        } else {
            Path {
                absolute: false,
                segments,
            }
        }
    }
}

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

#[derive(PartialEq, Copy, Clone, Eq, Hash)]
pub struct AstId {
    pub id: usize,
}

impl Display for AstId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.id)
    }
}

impl Debug for AstId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

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

impl BuiltinType {
    pub fn is_integer(&self) -> bool {
        match self {
            BuiltinType::U8
            | BuiltinType::I8
            | BuiltinType::U16
            | BuiltinType::I16
            | BuiltinType::U32
            | BuiltinType::I32
            | BuiltinType::U64
            | BuiltinType::I64
            | BuiltinType::U128
            | BuiltinType::I128
            | BuiltinType::USize
            | BuiltinType::ISize => true,
            _ => false,
        }
    }

    pub fn is_float(&self) -> bool {
        match self {
            BuiltinType::F32 | BuiltinType::F64 => true,
            _ => false,
        }
    }

    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float()
    }

    pub fn is_signed(&self) -> bool {
        match self {
            BuiltinType::I8
            | BuiltinType::I16
            | BuiltinType::I32
            | BuiltinType::I64
            | BuiltinType::I128
            | BuiltinType::ISize => true,
            _ => false,
        }
    }

    pub fn is_void(&self) -> bool {
        match self {
            BuiltinType::Void => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ty<'ast> {
    Placeholder(AstId),
    Extern(AstId),
    NamedType(ItemP<'ast>),
    Builtin(BuiltinType),
    Pointer(TyP<'ast>, bool),
    Dyn(bool),
    Slice(TyP<'ast>, bool),
    Array(TyP<'ast>, usize),
    Tuple(&'ast [TyP<'ast>]),
    Fn(&'ast [TyP<'ast>], TyP<'ast>),
    GenericType(ItemP<'ast>, &'ast [TyP<'ast>]),
}

impl<'ast> Ty<'ast> {
    pub fn canonical_type(&'ast self) -> TyP<'ast> {
        match self {
            Ty::Pointer(inner, _) => inner.canonical_type(),
            _ => self,
        }
    }
}

pub type TyP<'ast> = &'ast Ty<'ast>;

#[derive(Debug)]
pub enum Item<'ast> {
    Enum(Enum<'ast>),
    Struct(Struct<'ast>),
    Function(Function<'ast>),
    Static(Static<'ast>),
    Macro(Macro<'ast>),
    Intrinsic(Intrinsic),
}

impl<'ast> Item<'ast> {
    pub fn should_compile(&self) -> bool {
        match self {
            Item::Function(Function {
                placeholders,
                attributes,
                ..
            }) => placeholders.is_empty() && attributes.contains(&Attribute::Export),
            _ => false,
        }
    }
}

pub type ItemP<'ast> = &'ast ItemCell<'ast>;

impl<'ast> ItemCell<'ast> {
    pub fn assign(&self, value: Item<'ast>) {
        // Panic if we try to assign the same symbol twice
        self.contents
            .set(value)
            .expect("assigning the same symbol twice");
    }

    pub fn try_get(&'ast self) -> Option<&'ast Item<'ast>> {
        self.contents.get()
    }

    pub fn get(&'ast self) -> &'ast Item<'ast> {
        self.contents.get().unwrap()
    }

    pub fn get_function(&'ast self) -> &'ast Function<'ast> {
        match self.contents.get() {
            Some(Item::Function(f)) => f,
            _ => panic!("function expected"),
        }
    }

    pub fn get_struct(&'ast self) -> &'ast Struct<'ast> {
        match self.contents.get() {
            Some(Item::Struct(s)) => s,
            _ => panic!("struct expected"),
        }
    }

    pub fn get_macro(&'ast self) -> &'ast Macro<'ast> {
        match self.contents.get() {
            Some(Item::Macro(m)) => m,
            _ => panic!("macro expected"),
        }
    }
}

/// SymbolCell is a wrapper that allows us to build recursive structures incrementally.
/// This allows us to assign symbols to syntax early in name resolution and fill them in
/// later.
/// Symbols are immutable once they are assigned.
pub struct ItemCell<'ast> {
    pub id: AstId,
    pub contents: OnceCell<Item<'ast>>,
}

impl Hash for ItemCell<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Symbols have reference semantics. Two structs with the same fields
/// are not considered equal.
impl PartialEq for ItemCell<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ItemCell<'_> {}

impl Debug for ItemCell<'_> {
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

#[derive(Debug, Clone, Copy)]
pub struct Field<'ast> {
    pub id: AstId,
    pub name: &'ast str,
    pub typ: TyP<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy)]
pub struct EnumMember<'ast> {
    pub id: AstId,
    pub name: Option<&'ast str>,
    pub value: Option<ExprP<'ast>>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy)]
pub struct AssociatedFn<'ast> {
    pub name: &'ast str,
    pub item: ItemP<'ast>,
}

#[derive(Debug)]
pub struct Struct<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [AstId],
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub attributes: &'ast [Attribute],
    pub fields: &'ast [Field<'ast>],
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct Enum<'ast> {
    pub name: Option<&'ast str>,
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub attributes: &'ast [Attribute],
    pub members: &'ast [EnumMember<'ast>],
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy)]
pub struct Parameter<'ast> {
    pub id: AstId,
    pub typ: TyP<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct Intrinsic {
    pub kind: IntrinsicKind,
    pub span: Option<Span>,
    pub generic_count: usize,
    pub arg_count: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct MacroParameter {
    pub id: AstId,
    pub et_cetera: bool,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct Macro<'ast> {
    pub name: Option<&'ast str>,
    pub args: &'ast [MacroParameter],
    pub body: OnceCell<ExprP<'ast>>,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct Function<'ast> {
    pub name: Option<&'ast str>,
    pub attributes: &'ast [Attribute],
    pub placeholders: &'ast [AstId],
    pub args: &'ast [Parameter<'ast>],
    pub return_type: TyP<'ast>,
    pub body: Option<ExprP<'ast>>,
    pub span: Option<Span>,
    pub closure: bool,
}

#[derive(Debug)]
pub struct Static<'ast> {
    pub name: Option<&'ast str>,
    pub attributes: &'ast [Attribute],
    pub typ: Option<TyP<'ast>>,
    pub init: Option<ExprP<'ast>>,
    pub span: Option<Span>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct LetDeclaration<'ast> {
    pub id: AstId,
    pub typ: Option<TyP<'ast>>,
    pub value: Option<ExprP<'ast>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum StatementKind<'ast> {
    Expression(ExprP<'ast>),
    LetDeclaration(LetDeclaration<'ast>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Statement<'ast> {
    pub kind: StatementKind<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum BinOp {
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Neq,
    Lt,
    LEq,
    Gt,
    GEq,
    LShift,
    RShift,
    Plus,
    Minus,
    Mul,
    Div,
    Mod,
}

impl BinOp {
    pub fn is_comparison(&self) -> bool {
        match self {
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::LEq | BinOp::Gt | BinOp::GEq => true,
            _ => false,
        }
    }

    pub fn is_logical(&self) -> bool {
        match self {
            BinOp::And | BinOp::Or => true,
            _ => false,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Attribute {
    Export,
    ForceInline,
    Intrinsic,
    StaticConstructor,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Lit<'ast> {
    Str(&'ast [u8]),
    Int(u128, Option<BuiltinType>),
    Float(&'ast str, Option<BuiltinType>),
    Bool(bool),
    Null,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct FieldInitializer<'ast> {
    pub name: &'ast str,
    pub value: ExprP<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct DeferredFn<'ast> {
    pub placeholder: AstId,
    pub name: &'ast str,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum FnKind<'ast> {
    Normal(ItemP<'ast>),
    Defered(DeferredFn<'ast>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprKind<'ast> {
    Block(&'ast [Statement<'ast>], ExprP<'ast>),
    Binary(BinOp, ExprP<'ast>, ExprP<'ast>),
    Call(ExprP<'ast>, &'ast [ExprP<'ast>]),

    Fn(FnKind<'ast>, Option<&'ast [TyP<'ast>]>),

    Ref(ExprP<'ast>),
    Deref(ExprP<'ast>),
    Unary(UnOp, ExprP<'ast>),
    Assign(ExprP<'ast>, ExprP<'ast>),
    AssignOp(BinOp, ExprP<'ast>, ExprP<'ast>),
    Local(AstId),
    Static(ItemP<'ast>),
    EnumValue(ItemP<'ast>, AstId),
    Lit(Lit<'ast>),
    Loop(ExprP<'ast>),
    EtCetera(ExprP<'ast>),
    Break(Option<ExprP<'ast>>),
    Return(Option<ExprP<'ast>>),
    Defer(ExprP<'ast>),
    Continue,
    Tuple(&'ast [ExprP<'ast>]),
    Array(&'ast [ExprP<'ast>]),
    Struct(TyP<'ast>, &'ast [FieldInitializer<'ast>]),
    Field(ExprP<'ast>, &'ast str, Option<ItemP<'ast>>),
    TupleIndex(ExprP<'ast>, usize),
    Index(ExprP<'ast>, ExprP<'ast>),
    RangeIndex(ExprP<'ast>, Option<ExprP<'ast>>, Option<ExprP<'ast>>),
    If(ExprP<'ast>, ExprP<'ast>, ExprP<'ast>),
    Cast(ExprP<'ast>, TyP<'ast>),

    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub file: FileId,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Expr<'ast> {
    pub kind: ExprKind<'ast>,
    pub span: Option<Span>,
}

pub type ExprP<'ast> = &'ast Expr<'ast>;

impl_allocatable!(
    Expr<'_>,
    Ty<'_>,
    Statement<'_>,
    Field<'_>,
    Parameter<'_>,
    MacroParameter,
    ItemCell<'_>,
    FieldInitializer<'_>,
    AssociatedFn<'_>,
    EnumMember<'_>,
    Attribute,
    AstId
);
