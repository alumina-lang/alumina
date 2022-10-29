pub mod expressions;
pub mod lang;
pub mod macros;
pub mod maker;
pub mod rebind;
pub mod types;

use self::lang::LangItemKind;
use crate::common::{Allocatable, ArenaAllocatable, CodeErrorKind, FileId, Incrementable};
use crate::intrinsics::IntrinsicKind;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::BoundItemType;
use std::fmt::Display;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

use bumpalo::Bump;
use once_cell::unsync::OnceCell;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use crate::common::impl_allocatable;

#[derive(Clone)]
pub struct TestMetadata<'ast> {
    pub path: Path<'ast>,
    pub name: Path<'ast>,
    pub attributes: Vec<String>,
}

pub struct AstCtx<'ast> {
    pub arena: Bump,
    pub counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'ast>>>,
    lang_items: RefCell<HashMap<LangItemKind, ItemP<'ast>>>,
    test_metadata: RefCell<HashMap<ItemP<'ast>, TestMetadata<'ast>>>,
}

impl<'ast> AstCtx<'ast> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::new()),
            lang_items: RefCell::new(HashMap::new()),
            test_metadata: RefCell::new(HashMap::new()),
        }
    }

    pub fn make_id(&self) -> AstId {
        AstId {
            id: self.counter.increment(),
        }
    }

    pub fn lang_item(&self, kind: LangItemKind) -> Result<ItemP<'ast>, CodeErrorKind> {
        self.lang_items
            .borrow()
            .get(&kind)
            .copied()
            .ok_or(CodeErrorKind::MissingLangItem(kind))
    }

    pub fn lang_item_kind(&self, item: ItemP<'ast>) -> Option<LangItemKind> {
        self.lang_items
            .borrow()
            .iter()
            .find(|(_, v)| **v == item)
            .map(|(k, _)| k)
            .copied()
    }

    pub fn add_lang_item(&self, kind: LangItemKind, item: ItemP<'ast>) {
        self.lang_items.borrow_mut().insert(kind, item);
    }

    pub fn add_test_metadata(&'ast self, item: ItemP<'ast>, metadata: TestMetadata<'ast>) {
        self.test_metadata.borrow_mut().insert(item, metadata);
    }

    pub fn test_metadata(&self, item: ItemP<'ast>) -> Option<TestMetadata<'ast>> {
        self.test_metadata.borrow().get(&item).cloned()
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
        self.arena.alloc(ItemCell {
            id: self.make_id(),
            contents: OnceCell::new(),
        })
    }

    pub fn parse_path(&'ast self, path: &'_ str) -> Path<'ast> {
        let (path, absolute) = if path.starts_with("::") {
            (path.strip_prefix("::").unwrap(), true)
        } else {
            (path, false)
        };

        let segments: Vec<_> = path
            .split("::")
            .filter_map(|s| {
                if s.is_empty() {
                    None
                } else {
                    Some(PathSegment(s.alloc_on(self)))
                }
            })
            .collect();

        Path { absolute, segments }
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
        matches!(
            self,
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
                | BuiltinType::ISize
        )
    }

    pub fn to_signed(self) -> Option<BuiltinType> {
        let ret = match self {
            BuiltinType::I8
            | BuiltinType::I16
            | BuiltinType::I32
            | BuiltinType::I64
            | BuiltinType::I128
            | BuiltinType::ISize => self,
            BuiltinType::U8 => BuiltinType::I8,
            BuiltinType::U16 => BuiltinType::I16,
            BuiltinType::U32 => BuiltinType::I32,
            BuiltinType::U64 => BuiltinType::I64,
            BuiltinType::U128 => BuiltinType::I128,
            BuiltinType::USize => BuiltinType::ISize,
            _ => return None,
        };

        Some(ret)
    }

    pub fn to_unsigned(self) -> Option<BuiltinType> {
        let ret = match self {
            BuiltinType::U8
            | BuiltinType::U16
            | BuiltinType::U32
            | BuiltinType::U64
            | BuiltinType::U128
            | BuiltinType::USize => self,
            BuiltinType::I8 => BuiltinType::U8,
            BuiltinType::I16 => BuiltinType::U16,
            BuiltinType::I32 => BuiltinType::U32,
            BuiltinType::I64 => BuiltinType::U64,
            BuiltinType::I128 => BuiltinType::U128,
            BuiltinType::ISize => BuiltinType::USize,
            _ => return None,
        };

        Some(ret)
    }

    pub fn is_float(&self) -> bool {
        matches!(self, BuiltinType::F32 | BuiltinType::F64)
    }

    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float()
    }

    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            BuiltinType::I8
                | BuiltinType::I16
                | BuiltinType::I32
                | BuiltinType::I64
                | BuiltinType::I128
                | BuiltinType::ISize
        )
    }

    pub fn is_void(&self) -> bool {
        matches!(self, BuiltinType::Void)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Ty<'ast> {
    Placeholder(AstId),
    Protocol(ItemP<'ast>),
    NamedType(ItemP<'ast>),
    NamedFunction(ItemP<'ast>),
    Builtin(BuiltinType),
    Pointer(TyP<'ast>, bool),
    Slice(TyP<'ast>, bool),
    Dyn(&'ast [TyP<'ast>], bool),
    TypeOf(ExprP<'ast>),
    Array(TyP<'ast>, ExprP<'ast>),
    Tuple(&'ast [TyP<'ast>]),
    When(StaticIfCondition<'ast>, TyP<'ast>, TyP<'ast>),
    FunctionPointer(&'ast [TyP<'ast>], TyP<'ast>),
    FunctionProtocol(&'ast [TyP<'ast>], TyP<'ast>),
    Generic(TyP<'ast>, &'ast [TyP<'ast>]),
    Defered(Defered<'ast>),
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
    StructLike(StructLike<'ast>),
    TypeDef(TypeDef<'ast>),
    Protocol(Protocol<'ast>),
    Function(Function<'ast>),
    StaticOrConst(StaticOrConst<'ast>),
    Macro(Macro<'ast>),
    BuiltinMacro(BuiltinMacro),
    Intrinsic(Intrinsic),
}

impl<'ast> Item<'ast> {
    pub fn can_compile(&self) -> bool {
        match self {
            Item::Function(Function {
                placeholders,
                is_protocol_fn,
                ..
            }) => placeholders.is_empty() && !is_protocol_fn,
            Item::Enum(_) => true,
            Item::StructLike(StructLike { placeholders, .. }) => placeholders.is_empty(),
            _ => false,
        }
    }

    pub fn is_special(&self) -> bool {
        match self {
            Item::Function(Function {
                placeholders,
                is_protocol_fn,
                ..
            }) => placeholders.is_empty() && !is_protocol_fn,
            _ => false,
        }
    }

    pub fn should_compile(&self) -> bool {
        self.can_compile()
            && match self {
                Item::Function(Function { attributes, .. }) => {
                    attributes.contains(&Attribute::Test) || attributes.contains(&Attribute::Export)
                }
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

    pub fn get_struct_like(&'ast self) -> &'ast StructLike<'ast> {
        match self.contents.get() {
            Some(Item::StructLike(s)) => s,
            _ => panic!("struct or union expected"),
        }
    }

    pub fn get_protocol(&'ast self) -> &'ast Protocol<'ast> {
        match self.contents.get() {
            Some(Item::Protocol(p)) => p,
            _ => panic!("protocol expected"),
        }
    }

    pub fn get_typedef(&'ast self) -> &'ast TypeDef<'ast> {
        match self.contents.get() {
            Some(Item::TypeDef(t)) => t,
            _ => panic!("typedef expected"),
        }
    }

    pub fn is_struct_like(&self) -> bool {
        matches!(self.contents.get(), Some(Item::StructLike(_)))
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
    pub name: &'ast str,
    pub value: Option<ExprP<'ast>>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy)]
pub struct AssociatedFn<'ast> {
    pub name: &'ast str,
    pub item: ItemP<'ast>,
}

#[derive(Debug, Clone)]
pub struct MixinCell<'ast> {
    pub contents: OnceCell<&'ast [AssociatedFn<'ast>]>,
}

#[derive(Debug, Clone, Copy)]
pub struct Mixin<'ast> {
    pub placeholders: &'ast [Placeholder<'ast>],
    pub protocol: TyP<'ast>,
    pub span: Option<Span>,
    pub contents: &'ast MixinCell<'ast>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bound<'ast> {
    pub negated: bool,
    pub span: Option<Span>,
    pub typ: TyP<'ast>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProtocolBoundsKind {
    All,
    Any,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProtocolBounds<'ast> {
    pub kind: ProtocolBoundsKind,
    pub bounds: &'ast [Bound<'ast>],
}

#[derive(Debug, Clone, Copy)]
pub struct Placeholder<'ast> {
    pub id: AstId,
    pub bounds: ProtocolBounds<'ast>,
    pub default: Option<TyP<'ast>>,
}

#[derive(Debug)]
pub struct Protocol<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [Placeholder<'ast>],
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub attributes: &'ast [Attribute],
    pub is_local: bool,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct StructLike<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [Placeholder<'ast>],
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub mixins: &'ast [Mixin<'ast>],
    pub attributes: &'ast [Attribute],
    pub fields: &'ast [Field<'ast>],
    pub span: Option<Span>,
    pub is_local: bool,
    pub is_union: bool,
}

#[derive(Debug)]
pub struct TypeDef<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [Placeholder<'ast>],
    pub attributes: &'ast [Attribute],
    pub target: Option<TyP<'ast>>,
    pub is_local: bool,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct Enum<'ast> {
    pub name: Option<&'ast str>,
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub mixins: &'ast [Mixin<'ast>],
    pub attributes: &'ast [Attribute],
    pub members: &'ast [EnumMember<'ast>],
    pub is_local: bool,
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
    pub varargs: bool,
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
pub enum BuiltinMacroKind {
    Env,
    Concat,
    Line,
    Column,
    File,
    IncludeBytes,
    FormatArgs,
}

#[derive(Debug)]
pub struct BuiltinMacro {
    pub kind: BuiltinMacroKind,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub struct Function<'ast> {
    pub name: Option<&'ast str>,
    pub attributes: &'ast [Attribute],
    pub placeholders: &'ast [Placeholder<'ast>],
    pub args: &'ast [Parameter<'ast>],
    pub return_type: TyP<'ast>,
    pub body: Option<ExprP<'ast>>,
    pub span: Option<Span>,
    pub is_local: bool,
    pub varargs: bool,
    pub is_protocol_fn: bool,
}

#[derive(Debug)]
pub struct StaticOrConst<'ast> {
    pub name: Option<&'ast str>,
    pub attributes: &'ast [Attribute],
    pub placeholders: &'ast [Placeholder<'ast>],
    pub typ: Option<TyP<'ast>>,
    pub init: Option<ExprP<'ast>>,
    pub span: Option<Span>,
    pub is_local: bool,
    pub is_const: bool,
    pub r#extern: bool,
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
        matches!(
            self,
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::LEq | BinOp::Gt | BinOp::GEq
        )
    }

    pub fn is_logical(&self) -> bool {
        matches!(self, BinOp::And | BinOp::Or)
    }
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Attribute {
    Export,
    Test,
    Cold,
    TestMain,
    Inline,
    Align(usize),
    Packed,
    Transparent,
    NoInline,
    ThreadLocal,
    Builtin,
    AlwaysInline,
    InlineDuringMono,
    Intrinsic,
    StaticConstructor,
    LinkName(usize, [u8; 255]),
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

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct Defered<'ast> {
    pub typ: TyP<'ast>,
    pub name: &'ast str,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ClosureBinding<'ast> {
    pub id: AstId,
    pub value: ExprP<'ast>,
    pub binding_type: BoundItemType,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum FnKind<'ast> {
    Normal(ItemP<'ast>),
    Closure(&'ast [ClosureBinding<'ast>], ItemP<'ast>),
    Defered(Defered<'ast>),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct StaticIfCondition<'ast> {
    pub typ: TyP<'ast>,
    pub bounds: ProtocolBounds<'ast>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprKind<'ast> {
    Block(&'ast [Statement<'ast>], ExprP<'ast>),
    Binary(BinOp, ExprP<'ast>, ExprP<'ast>),
    Call(ExprP<'ast>, &'ast [ExprP<'ast>]),

    Defered(Defered<'ast>),
    DeferedMacro(ItemP<'ast>, &'ast [ExprP<'ast>]),

    Fn(FnKind<'ast>, Option<&'ast [TyP<'ast>]>),

    Ref(ExprP<'ast>),
    Deref(ExprP<'ast>),
    Unary(UnOp, ExprP<'ast>),
    Assign(ExprP<'ast>, ExprP<'ast>),
    AssignOp(BinOp, ExprP<'ast>, ExprP<'ast>),
    Local(AstId),
    Static(ItemP<'ast>, Option<&'ast [TyP<'ast>]>),
    Const(ItemP<'ast>, Option<&'ast [TyP<'ast>]>),
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
    BoundParam(AstId, AstId, BoundItemType),
    Field(ExprP<'ast>, &'ast str, Option<ItemP<'ast>>),
    TupleIndex(ExprP<'ast>, usize),
    Index(ExprP<'ast>, ExprP<'ast>),
    Range(Option<ExprP<'ast>>, Option<ExprP<'ast>>, bool),
    If(ExprP<'ast>, ExprP<'ast>, ExprP<'ast>),
    StaticIf(StaticIfCondition<'ast>, ExprP<'ast>, ExprP<'ast>),
    Cast(ExprP<'ast>, TyP<'ast>),

    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
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
    Mixin<'_>,
    Parameter<'_>,
    MacroParameter,
    ItemCell<'_>,
    FieldInitializer<'_>,
    Bound<'_>,
    AssociatedFn<'_>,
    ClosureBinding<'_>,
    EnumMember<'_>,
    Placeholder<'_>,
    Attribute,
    AstId
);
