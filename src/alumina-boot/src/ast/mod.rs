pub mod expressions;
pub mod format;
pub mod lang;
pub mod macros;
pub mod maker;
pub mod pretty;
pub mod rebind;
pub mod serialization;
pub mod types;

use crate::ast::lang::LangItemKind;
use crate::common::{
    impl_allocatable, Allocatable, ArenaAllocatable, CodeDiagnostic, FileId, HashMap, HashSet,
    Incrementable,
};
use crate::intrinsics::IntrinsicKind;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::BoundItemType;

use crate::ast::serialization::{AstDeserializer, AstSerializable, AstSerializer};

use alumina_boot_macros::AstSerializable;

use bumpalo::Bump;
use once_cell::unsync::OnceCell;

use std::cell::{Cell, RefCell};
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::io::{Read, Write};

#[derive(Clone, AstSerializable)]
pub struct TestMetadata<'ast> {
    pub path: Path<'ast>,
    pub name: Path<'ast>,
    pub attributes: Vec<String>,
}

pub struct AstCtx<'ast> {
    pub arena: Bump,
    pub counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'ast>>>,
    strings: RefCell<HashSet<&'ast str>>,
    lang_items: RefCell<HashMap<LangItemKind, ItemP<'ast>>>,
    local_names: RefCell<HashMap<AstId, &'ast str>>,
    test_metadata: RefCell<HashMap<ItemP<'ast>, TestMetadata<'ast>>>,
}

impl<'ast> AstCtx<'ast> {
    pub fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::default()),
            strings: RefCell::new(HashSet::default()),
            lang_items: RefCell::new(HashMap::default()),
            local_names: RefCell::new(HashMap::default()),
            test_metadata: RefCell::new(HashMap::default()),
        }
    }

    pub fn make_id(&self) -> AstId {
        AstId {
            id: self.counter.increment(),
        }
    }

    pub fn lang_item(&self, kind: LangItemKind) -> Result<ItemP<'ast>, CodeDiagnostic> {
        self.lang_items
            .borrow()
            .get(&kind)
            .copied()
            .ok_or(CodeDiagnostic::MissingLangItem(kind))
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

    pub fn intern_str(&'ast self, name: &'_ str) -> &'ast str {
        if let Some(key) = self.strings.borrow().get(name) {
            return key;
        }

        let inner = self.arena.alloc_str(name);
        self.strings.borrow_mut().insert(inner);

        inner
    }

    pub fn add_local_name(&'ast self, id: AstId, name: &'ast str) {
        self.local_names.borrow_mut().insert(id, name);
    }

    pub fn local_name(&self, id: AstId) -> Option<&'ast str> {
        self.local_names.borrow().get(&id).copied()
    }

    pub fn test_metadata(&self, item: ItemP<'ast>) -> Option<TestMetadata<'ast>> {
        self.test_metadata.borrow().get(&item).cloned()
    }

    pub fn intern_type(&'ast self, ty: Ty<'ast>) -> TyP<'ast> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return key;
        }

        let inner = self.arena.alloc(ty);
        self.types.borrow_mut().insert(inner);

        inner
    }

    pub fn make_item(&'ast self) -> ItemP<'ast> {
        self.arena.alloc(ItemCell {
            id: self.make_id(),
            contents: OnceCell::new(),
        })
    }

    pub fn make_item_with(&'ast self, id: AstId) -> ItemP<'ast> {
        self.arena.alloc(ItemCell {
            id,
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
        ctx.intern_str(self)
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

impl<'a> AstSerializable<'a> for AstId {
    fn serialize<W: Write>(
        &self,
        serializer: &mut AstSerializer<'a, W>,
    ) -> crate::ast::serialization::Result<()> {
        self.id.serialize(serializer)
    }

    fn deserialize<R: Read>(
        deserializer: &mut AstDeserializer<'a, R>,
    ) -> crate::ast::serialization::Result<Self> {
        let id = <usize as AstSerializable>::deserialize(deserializer)?;
        Ok(deserializer.context().map_ast_id(AstId { id }))
    }
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

#[derive(Debug, PartialEq, Copy, Clone, Eq, Hash, AstSerializable)]
pub enum BuiltinType {
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
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, AstSerializable)]
pub enum Ty<'ast> {
    Placeholder(AstId),
    Item(ItemP<'ast>),
    Builtin(BuiltinType),
    Pointer(TyP<'ast>, bool),
    Slice(TyP<'ast>, bool),
    Dyn(&'ast [TyP<'ast>], bool),
    TypeOf(ExprP<'ast>),
    Array(TyP<'ast>, ExprP<'ast>),
    Tuple(&'ast [TyP<'ast>]),
    When(ExprP<'ast>, TyP<'ast>, TyP<'ast>),
    FunctionPointer(&'ast [TyP<'ast>], TyP<'ast>),
    FunctionProtocol(&'ast [TyP<'ast>], TyP<'ast>),
    Generic(TyP<'ast>, &'ast [TyP<'ast>]),
    Tag(&'ast str, TyP<'ast>),
    Defered(Defered<'ast>),
}

impl<'ast> Ty<'ast> {
    pub fn void() -> Ty<'ast> {
        Ty::Tuple(&[])
    }

    pub fn is_void(&self) -> bool {
        matches!(self, Ty::Tuple(tys) if tys.is_empty())
    }

    pub fn canonical_type(&'ast self) -> TyP<'ast> {
        match self {
            Ty::Pointer(inner, _) => inner.canonical_type(),
            _ => self,
        }
    }

    pub fn is_dynamic(&self) -> bool {
        match self {
            Ty::Tag("dynamic", _) => true,
            Ty::Tag(_, inner) => inner.is_dynamic(),
            Ty::Placeholder(_) | Ty::TypeOf(_) | Ty::When(_, _, _) | Ty::Defered(_) => true,
            Ty::Item(_) | Ty::Builtin(_) => false,
            Ty::Pointer(inner, _) | Ty::Slice(inner, _) | Ty::Array(inner, _) => inner.is_dynamic(),
            Ty::Dyn(inner, _) | Ty::Tuple(inner) => inner.iter().any(|s| s.is_dynamic()),
            Ty::FunctionPointer(params, ret) | Ty::FunctionProtocol(params, ret) => {
                params.iter().any(|s| s.is_dynamic()) || ret.is_dynamic()
            }
            Ty::Generic(base, params) => base.is_dynamic() || params.iter().any(|s| s.is_dynamic()),
        }
    }
}

pub type TyP<'ast> = &'ast Ty<'ast>;
/*
impl<'ast> AstSerializable<'ast> for TyP<'ast> {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> crate::ast::serialization::Result<()> {
        (*self).serialize(serializer)
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> crate::ast::serialization::Result<Self> {
        let ty = <Ty<'ast> as AstSerializable>::deserialize(deserializer)?;

        Ok(deserializer.ast.intern_type(ty))
    }
}
*/
#[derive(Debug, AstSerializable)]
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

    pub fn should_compile(&self) -> bool {
        self.can_compile()
            && match self {
                Item::Function(Function { attributes, .. }) => {
                    attributes.contains(&Attribute::Test) || attributes.contains(&Attribute::Export)
                }
                _ => false,
            }
    }

    pub fn is_main_candidate(&self) -> bool {
        match self {
            Item::Function(Function { attributes, .. }) => attributes.contains(&Attribute::Main),
            _ => false,
        }
    }

    pub fn is_test_main_candidate(&self) -> bool {
        match self {
            Item::Function(Function { attributes, .. }) => {
                attributes.contains(&Attribute::TestMain)
            }
            _ => false,
        }
    }
}

pub type ItemP<'ast> = &'ast ItemCell<'ast>;

impl<'ast> AstSerializable<'ast> for ItemP<'ast> {
    fn serialize<W: Write>(
        &self,
        serializer: &mut AstSerializer<'ast, W>,
    ) -> crate::ast::serialization::Result<()> {
        self.id.serialize(serializer)
    }

    fn deserialize<R: Read>(
        deserializer: &mut AstDeserializer<'ast, R>,
    ) -> crate::ast::serialization::Result<Self> {
        let id = AstId::deserialize(deserializer)?;

        Ok(deserializer.context().get_cell(id))
    }
}

impl<'ast> ItemCell<'ast> {
    pub fn assign(&self, value: Item<'ast>) {
        // Panic if we try to assign the same item twice
        self.contents
            .set(value)
            .expect("assigning the same item twice");
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

    pub fn get_enum(&'ast self) -> &'ast Enum<'ast> {
        match self.contents.get() {
            Some(Item::Enum(t)) => t,
            _ => panic!("enum expected"),
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

/// ItemCell is a wrapper that allows us to build recursive structures incrementally.
/// This allows us to assign items to syntax early in name resolution and fill them in
/// later.
/// Items are immutable once they are assigned.
pub struct ItemCell<'ast> {
    pub id: AstId,
    pub contents: OnceCell<Item<'ast>>,
}

impl Hash for ItemCell<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Items have reference semantics. Two structs with the same fields
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

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct Field<'ast> {
    pub id: AstId,
    pub name: &'ast str,
    pub typ: TyP<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct EnumMember<'ast> {
    pub id: AstId,
    pub name: &'ast str,
    pub value: Option<ExprP<'ast>>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct AssociatedFn<'ast> {
    pub name: &'ast str,
    pub item: ItemP<'ast>,
}

#[derive(Debug, Clone, AstSerializable)]
pub struct MixinCell<'ast> {
    pub contents: OnceCell<&'ast [AssociatedFn<'ast>]>,
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct Mixin<'ast> {
    pub placeholders: &'ast [Placeholder<'ast>],
    pub protocol: TyP<'ast>,
    pub span: Option<Span>,
    pub contents: &'ast MixinCell<'ast>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, AstSerializable)]
pub struct Bound<'ast> {
    pub negated: bool,
    pub span: Option<Span>,
    pub typ: TyP<'ast>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, AstSerializable)]
pub enum ProtocolBoundsKind {
    All,
    Any,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, AstSerializable)]
pub struct ProtocolBounds<'ast> {
    pub kind: ProtocolBoundsKind,
    pub bounds: &'ast [Bound<'ast>],
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct Placeholder<'ast> {
    pub id: AstId,
    pub bounds: ProtocolBounds<'ast>,
    pub span: Option<Span>,
    pub default: Option<TyP<'ast>>,
}

#[derive(Debug, AstSerializable)]
pub struct Protocol<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [Placeholder<'ast>],
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub attributes: &'ast [Attribute<'ast>],
    pub is_local: bool,
    pub span: Option<Span>,
}

#[derive(Debug, AstSerializable)]
pub struct StructLike<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [Placeholder<'ast>],
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub mixins: &'ast [Mixin<'ast>],
    pub attributes: &'ast [Attribute<'ast>],
    pub fields: &'ast [Field<'ast>],
    pub span: Option<Span>,
    pub is_local: bool,
    pub is_union: bool,
}

#[derive(Debug, AstSerializable)]
pub struct TypeDef<'ast> {
    pub name: Option<&'ast str>,
    pub placeholders: &'ast [Placeholder<'ast>],
    pub attributes: &'ast [Attribute<'ast>],
    pub target: Option<TyP<'ast>>,
    pub is_local: bool,
    pub span: Option<Span>,
}

#[derive(Debug, AstSerializable)]
pub struct Enum<'ast> {
    pub name: Option<&'ast str>,
    pub associated_fns: &'ast [AssociatedFn<'ast>],
    pub mixins: &'ast [Mixin<'ast>],
    pub attributes: &'ast [Attribute<'ast>],
    pub members: &'ast [EnumMember<'ast>],
    pub is_local: bool,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct Parameter<'ast> {
    pub id: AstId,
    pub typ: TyP<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, AstSerializable)]
pub struct Intrinsic {
    pub kind: IntrinsicKind,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub struct MacroParameter {
    pub id: AstId,
    pub et_cetera: bool,
    pub span: Option<Span>,
}

#[derive(Debug, AstSerializable)]
pub struct Macro<'ast> {
    pub name: Option<&'ast str>,
    pub args: &'ast [MacroParameter],
    pub body: OnceCell<ExprP<'ast>>,
    pub span: Option<Span>,
}

#[derive(Debug, AstSerializable)]
pub enum BuiltinMacroKind {
    Env,
    Concat,
    Line,
    Column,
    File,
    Cfg,
    IncludeBytes,
    FormatArgs,
    Bind,
    Reduce,
    Stringify,
}

#[derive(Debug, AstSerializable)]
pub struct BuiltinMacro {
    pub kind: BuiltinMacroKind,
    pub span: Option<Span>,
}

#[derive(Debug, AstSerializable)]
pub struct Function<'ast> {
    pub name: Option<&'ast str>,
    pub attributes: &'ast [Attribute<'ast>],
    pub placeholders: &'ast [Placeholder<'ast>],
    pub args: &'ast [Parameter<'ast>],
    pub return_type: TyP<'ast>,
    pub body: Option<ExprP<'ast>>,
    pub span: Option<Span>,
    pub is_local: bool,
    pub is_lambda: bool,
    pub varargs: bool,
    pub is_protocol_fn: bool,
}

#[derive(Debug, AstSerializable)]
pub struct StaticOrConst<'ast> {
    pub name: Option<&'ast str>,
    pub attributes: &'ast [Attribute<'ast>],
    pub placeholders: &'ast [Placeholder<'ast>],
    pub typ: Option<TyP<'ast>>,
    pub init: Option<ExprP<'ast>>,
    pub span: Option<Span>,
    pub is_local: bool,
    pub is_const: bool,
    pub r#extern: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub struct LetDeclaration<'ast> {
    pub id: AstId,
    pub typ: Option<TyP<'ast>>,
    pub value: Option<ExprP<'ast>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub enum StatementKind<'ast> {
    Expression(ExprP<'ast>),
    LetDeclaration(LetDeclaration<'ast>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub struct Statement<'ast> {
    pub kind: StatementKind<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, AstSerializable)]
pub enum Attribute<'ast> {
    Export,
    Test,
    Cold,
    TestMain,
    Main,
    Inline,
    Align(usize),
    Packed(usize),
    ConstOnly,
    NoConst,
    MustUse,
    Transparent,
    NoInline,
    ThreadLocal,
    Builtin,
    AlwaysInline,
    InlineDuringMono,
    Intrinsic,
    StaticConstructor,
    LinkName(&'ast str),
}

impl<'ast> Attribute<'ast> {
    pub fn realloc_on<'new, F>(&'ast self, f: F) -> Attribute<'new>
    where
        F: Fn(&'ast str) -> &'new str,
    {
        match self {
            Attribute::LinkName(s) => Attribute::LinkName(f(s)),
            Attribute::Export => Attribute::Export,
            Attribute::Test => Attribute::Test,
            Attribute::Cold => Attribute::Cold,
            Attribute::TestMain => Attribute::TestMain,
            Attribute::Main => Attribute::Main,
            Attribute::Inline => Attribute::Inline,
            Attribute::Align(i) => Attribute::Align(*i),
            Attribute::Packed(i) => Attribute::Packed(*i),
            Attribute::MustUse => Attribute::MustUse,
            Attribute::Transparent => Attribute::Transparent,
            Attribute::NoInline => Attribute::NoInline,
            Attribute::ThreadLocal => Attribute::ThreadLocal,
            Attribute::Builtin => Attribute::Builtin,
            Attribute::AlwaysInline => Attribute::AlwaysInline,
            Attribute::InlineDuringMono => Attribute::InlineDuringMono,
            Attribute::Intrinsic => Attribute::Intrinsic,
            Attribute::StaticConstructor => Attribute::StaticConstructor,
            Attribute::ConstOnly => Attribute::ConstOnly,
            Attribute::NoConst => Attribute::NoConst,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
}

#[derive(Debug, Clone, PartialEq, Copy, Eq, Hash, AstSerializable)]
pub enum Lit<'ast> {
    Str(&'ast [u8]),
    Int(bool, u128, Option<BuiltinType>),
    Float(&'ast str, Option<BuiltinType>),
    Bool(bool),
    Null,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub struct FieldInitializer<'ast> {
    pub name: &'ast str,
    pub value: ExprP<'ast>,
    pub span: Option<Span>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy, AstSerializable)]
pub struct Defered<'ast> {
    pub typ: TyP<'ast>,
    pub name: &'ast str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub struct ClosureBinding<'ast> {
    pub id: AstId,
    pub value: ExprP<'ast>,
    pub binding_type: BoundItemType,
    pub span: Option<Span>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub enum FnKind<'ast> {
    Normal(ItemP<'ast>),
    Closure(&'ast [ClosureBinding<'ast>], ItemP<'ast>),
    Defered(Defered<'ast>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub enum ExprKind<'ast> {
    Block(&'ast [Statement<'ast>], ExprP<'ast>),
    Binary(BinOp, ExprP<'ast>, ExprP<'ast>),
    Call(ExprP<'ast>, &'ast [ExprP<'ast>]),

    Defered(Defered<'ast>),

    Macro(ItemP<'ast>, &'ast [ExprP<'ast>]),
    MacroInvocation(ExprP<'ast>, &'ast [ExprP<'ast>]),

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
    Field(
        ExprP<'ast>,
        &'ast str,
        Option<ItemP<'ast>>,
        Option<&'ast [TyP<'ast>]>,
    ),
    TupleIndex(ExprP<'ast>, usize),
    Index(ExprP<'ast>, ExprP<'ast>),
    Range(Option<ExprP<'ast>>, Option<ExprP<'ast>>, bool),
    If(ExprP<'ast>, ExprP<'ast>, ExprP<'ast>),
    TypeCheck(ExprP<'ast>, TyP<'ast>),
    StaticIf(ExprP<'ast>, ExprP<'ast>, ExprP<'ast>),
    Cast(ExprP<'ast>, TyP<'ast>),
    Tag(&'ast str, ExprP<'ast>),

    Void,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, AstSerializable)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: Option<usize>,
    pub file: FileId,
}

impl Span {
    pub fn from_node(file: FileId, node: tree_sitter::Node<'_>) -> Self {
        Self {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: Some(node.start_position().column),
            file,
        }
    }

    pub fn contains(&self, other: &Span) -> bool {
        self.start <= other.start && self.end >= other.end && self.file == other.file
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, AstSerializable)]
pub struct Expr<'ast> {
    pub kind: ExprKind<'ast>,
    pub span: Option<Span>,
}

pub type ExprP<'ast> = &'ast Expr<'ast>;

#[derive(Default, Copy, Clone)]
pub struct MacroCtx {
    pub in_a_macro: bool,
    pub has_et_cetera: bool,
}

impl MacroCtx {
    pub fn for_macro(has_et_cetera: bool) -> Self {
        Self {
            in_a_macro: true,
            has_et_cetera,
        }
    }
}

impl_allocatable!(
    Expr<'_>,
    Ty<'_>,
    Statement<'_>,
    Field<'_>,
    Mixin<'_>,
    Parameter<'_>,
    MacroParameter,
    ItemCell<'_>,
    MixinCell<'_>,
    FieldInitializer<'_>,
    Bound<'_>,
    AssociatedFn<'_>,
    ClosureBinding<'_>,
    EnumMember<'_>,
    Placeholder<'_>,
    Attribute<'_>,
    AstId
);
