use std::backtrace::Backtrace;
use std::cell::RefCell;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::io;
use std::rc::Rc;
use std::result::Result;
use strum_macros::AsRefStr;
use strum_macros::VariantNames;
use thiserror::Error;
use tree_sitter::Node;

macro_rules! ice {
    ($diag:expr, $why:literal) => {{
        return Err($diag.err(CodeDiagnostic::InternalError(
            $why.to_string(),
            std::backtrace::Backtrace::capture().into(),
        )));
    }};
}

pub(crate) use ice;

pub type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;
pub type HashSet<T> = rustc_hash::FxHashSet<T>;
pub type IndexMap<K, V> =
    indexmap::IndexMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
pub type IndexSet<K> = indexmap::IndexSet<K, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

/// A clonable (Rc) wrapper using pointer equality for `Hash` and `PartialEq`
pub struct ByRef<T>(pub Rc<T>);

impl<T> Hash for ByRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}
impl<T> PartialEq for ByRef<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl<T> Eq for ByRef<T> {}
impl<T: Debug> Debug for ByRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl<T: Display> Display for ByRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl<T> From<T> for ByRef<T> {
    fn from(t: T) -> Self {
        Self(Rc::new(t))
    }
}
impl<T> Clone for ByRef<T> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

#[derive(Debug, Error)]
pub enum AluminaError {
    #[error("code errors: {0:?}")]
    CodeErrors(Vec<CodeError>),
    #[error("io error: {0}")]
    Io(#[from] io::Error),
    #[error("serialization error: {0}")]
    Serialization(#[from] crate::ast::serialization::Error),
    #[error("{0}")]
    WalkDir(#[from] walkdir::Error),
}

/// Main enum for all errors and warnings that can occur during compilation
#[derive(AsRefStr, VariantNames, Debug, Error, Clone, Hash, PartialEq, Eq)]
#[strum(serialize_all = "snake_case")]
pub enum CodeDiagnostic {
    // Errors
    #[error("syntax error: unexpected `{}`", .0)]
    ParseError(String),
    #[error("syntax error: missing `{}`", .0)]
    ParseErrorMissing(String),
    #[error("unexpected `{}` here", .0)]
    Unexpected(String),
    #[error("could not resolve the path `{}`", .0)]
    UnresolvedPath(String),
    #[error("cycle detected while resolving aliases")]
    CycleDetected,
    #[error("duplicate name `{}`", .0)]
    DuplicateName(String),
    #[error("invalid literal")]
    InvalidLiteral,
    #[error("character literals must be exactly one byte")]
    InvalidCharLiteral,
    #[error("{} generic parameters expected, {} found" , .0, .1)]
    GenericParamCountMismatch(usize, usize),
    #[error("only enums and structs can have generic parameters")]
    UnexpectedGenericParams,
    #[error("... can only be used inside a tuple")]
    EtCeteraExprInUnsupported,
    #[error("... can only be used inside a tuple type or fn/Fn type")]
    EtCeteraInUnsupported,
    #[error("... can only be used on something that is a tuple")]
    EtCeteraOnNonTuple,
    #[error("type is recursive without indirection")]
    RecursiveWithoutIndirection,
    #[error("type hint required")]
    TypeHintRequired,
    #[error("type mismatch: `{}` expected, `{}` found", .0, .1)]
    TypeMismatch(String, String),
    #[error("branches have incompatible types (`{}`, `{}`)", .0, .1)]
    MismatchedBranchTypes(String, String),
    #[error("invalid escape sequence")]
    InvalidEscapeSequence,
    #[error("invalid attribute")]
    InvalidAttribute,
    #[error("invalid attribute ({})", .0)]
    InvalidAttributeDetail(String),
    #[error("duplicate attribute `{}`", .0)]
    DuplicateAttribute(String),
    #[error("cannot perform {:?} between `{}` and `{}`", .0, .1, .2)]
    InvalidBinOp(crate::ast::BinOp, String, String),
    #[error("cannot perform {:?} on `{}`", .0, .1)]
    InvalidUnOp(crate::ast::UnOp, String),
    #[error("cannot assign to rvalue")]
    CannotAssignToRValue,
    #[error("cannot assign to const")]
    CannotAssignToConst,
    #[error("cannot cast `{}` into `{}`", .0, .1)]
    InvalidCast(String, String),
    #[error("break outside of loop")]
    BreakOutsideOfLoop,
    #[error("continue outside of loop")]
    ContinueOutsideOfLoop,
    #[error("expected {} arguments, found {}", .0, .1)]
    ParamCountMismatch(usize, usize),
    #[error("tuple index out of bounds")]
    TupleIndexOutOfBounds,
    #[error("function or static expected")]
    FunctionOrStaticExpectedHere,
    #[error("unexpected generic arguments (is this a method that needs to be called?)")]
    UnexpectedGenericArgs,
    #[error("could not resolve item `{}`", .0)]
    UnresolvedItem(String),
    #[error("duplicate field `{}` in struct initializer", .0)]
    DuplicateFieldInitializer(String),
    #[error("expected a struct-like type here")]
    StructLikeExpectedHere,
    #[error("method `{}` not found on `{}`", .0, .1)]
    MethodNotFound(String, String),
    #[error("cannot be called as a method")]
    NotAMethod,
    #[error("default case must be last in a switch expression")]
    DefaultCaseMustBeLast,
    #[error("cannot reference `{}` in a nested function", .0)]
    CannotReferenceLocal(String),
    #[error("missing lang item: {:?}", .0)]
    MissingLangItem(Lang),
    #[error("only slices can be range-indexed")]
    RangeIndexNonSlice,
    #[error("internal error: {}", .0)]
    InternalError(String, ByRef<Backtrace>),
    // This error is a compiler bug if it happens on its own, but it can pop up when
    // we abort early due to a previous error.
    #[error("local with unknown type")]
    LocalWithUnknownType,
    #[error("unsupported ABI {:?}", .0)]
    UnsupportedABI(String),
    #[error("unknown intrinsic `{}`", .0)]
    UnknownIntrinsic(String),
    #[error("unknown lang item {}", .0)]
    UnknownLangItem(String),
    #[error("this cannot be a lang item")]
    CannotBeALangItem,
    #[error("cannot take address of a compiler intrinsic")]
    IntrinsicsAreSpecialMkay,
    #[error("extern \"C\" functions cannot have generic parameters")]
    ExternCGenericParams,
    #[error("constant string expected")]
    ConstantStringExpected,
    #[error("this expression is not evaluable at compile time ({})", .0)]
    CannotConstEvaluate(ConstEvalErrorKind),
    #[error("values of enum variants can only be integers")]
    InvalidValueForEnumVariant,
    #[error("{}", .0)]
    UserDefined(String),
    #[error("{}", .0)]
    ConstMessage(String),
    #[error("cannot defer inside a defered expression")]
    DeferInDefer,
    #[error("cannot yield inside a defered expression")]
    YieldInDefer,
    #[error("`$...` expressions can only be used in macros")]
    MacroEtCeteraOutsideOfMacro,
    #[error("`$` identifiers can only be used in macros")]
    DollaredOutsideOfMacro,
    #[error("{} is not a pointer type", .0)]
    NotAPointer(String),
    #[error("{} is not a tuple type", .0)]
    NotATuple(String),
    #[error("this macro does not have any `...` arguments")]
    NoMacroEtCeteraArgs,
    #[error("macro can have at most one `...` parameter")]
    MultipleMacroEtCeteras,
    #[error("recursive macro calls are not allowed")]
    RecursiveMacroCall,
    #[error("expression is not a macro")]
    NotAMacro,
    #[error("not enough macro arguments, at least {} expected", .0)]
    NotEnoughMacroArguments(usize),
    #[error("nested `$...` expansions are not supported (yet)")]
    MacroEtCeteraInMacroEtCetera,
    #[error("`$...` expansion is not allowed in this position")]
    CannotMacroEtCeteraHere,
    #[error("unexpanded macro (hint: append `!` to invoke it)")]
    IsAMacro,
    #[error("cyclic dependency during static initialization")]
    RecursiveStaticInitialization,
    #[error("can only do that in function scope")]
    NotInAFunctionScope,
    #[error("yield can only be used in a coroutine")]
    YieldOutsideOfCoroutine,
    #[error("unknown builtin macro `{}`", .0)]
    UnknownBuiltinMacro(String),
    #[error("type is not a protocol")]
    NotAProtocol,
    #[error("function must have a body")]
    FunctionMustHaveBody,
    #[error("protocol functions cannot be extern")]
    ProtocolFnsCannotBeExtern,
    #[error("varargs functions can only be extern")]
    VarArgsCanOnlyBeExtern,
    #[error("coroutines cannot be extern")]
    ExternCoroutine,
    #[error("coroutines cannot be protocol functions")]
    ProtocolCoroutine,
    #[error("coroutines must have Coroutine<_, _> as return type")]
    CoroutineReturnType,
    #[error("type `{}` matches `{}`, which it should not", .0, .1)]
    ProtocolMatch(String, String),
    #[error("type `{}` does not match `{}`", .0, .1)]
    ProtocolMismatch(String, String),
    #[error("type `{}` does not match `{}` ({})", .0, .1, .2)]
    ProtocolMismatchDetail(String, String, String),
    #[error("recursive protocol bounds are not supported")]
    CyclicProtocolBound,
    #[error("multiple `main` functions found")]
    MultipleMainFunctions,
    #[error("cyclic dependency during type resolution")]
    UnpopulatedItem,
    #[error(
        "generic type parameters cannot be used in this context (did you mean to call a function?)"
    )]
    GenericArgsInPath,
    #[error("this is not a type you can actually use, sorry")]
    BuiltinTypesAreSpecialMkay,
    #[error("invalid type operator")]
    InvalidTypeOperator,
    #[error("transparent structs and unions must have exactly one field")]
    InvalidTransparent,

    #[error("cannot determine source span")]
    NoSpanInformation,
    #[error("cannot have an `impl` block without a corresponding type")]
    NoFreeStandingImpl,
    #[error("this item cannot be a test")]
    CannotBeATest,
    #[error("test cases must have 0 parameters and return void")]
    InvalidTestCaseSignature,
    #[error("extern statics cannot have initializers")]
    ExternStaticMustHaveType,
    #[error("extern statics cannot be generic")]
    ExternStaticCannotBeGeneric,
    #[error("can only bind local variables")]
    CanOnlyCloseOverLocals,
    #[error("anonymous functions that bind environment variables cannot be coerced to a function pointer")]
    ClosuresAreNotFns,
    #[error("dyn requires a protocol")]
    NonProtocolDyn,
    #[error("builtin protocols cannot be used with `dyn`")]
    BuiltinProtocolDyn,
    #[error("protocols containing generic functions can only be used as mixins")]
    MixinOnlyProtocol,
    #[error("indirect `dyn` pointers are not supported")]
    IndirectDyn,
    #[error("signature of `{}` is incompatible with virtual dispatch", .0)]
    NonDynnableFunction(String),
    #[error("invalid format string ({})", .0)]
    InvalidFormatString(String),
    #[error("cannot read file `{}`", .0)]
    CannotReadFile(String),
    #[error("type alias must have a target")] // unless it is a blessed builtin :)
    TypedefWithoutTarget,
    #[error("type with infinite size (recursive type without indirection)")]
    TypeWithInfiniteSize,
    #[error("integer literal out of range ({} does not fit into {})", .0, .1)]
    IntegerOutOfRange(String, String),
    #[error("float literal out of range ({} does not fit into {})", .0, .1)]
    FloatOutOfRange(String, String),
    #[error("`#[align(...)]` cannot be used together with `#[packed]`")]
    AlignAndPacked,
    // IR inlining is very restricitve at the moment, these may eventually be removed
    #[error("cannot IR-inline functions that use variables")]
    IrInlineLocalDefs,
    #[error("cannot IR-inline functions that use flow control")]
    IrInlineFlowControl,
    #[error("cannot IR-inline functions that can return early")]
    IrInlineEarlyReturn,
    #[error("cannot define new items in a macro body (yet)")]
    MacrosCannotDefineItems,
    #[error("anonymous functions are not supported in a macro body (yet)")]
    MacrosCannotDefineLambdas,
    #[error("{}", .0)]
    ConstPanic(String),
    // This is an error unlike ZstPointerOffset, which is just a warning. If you think about it,
    // it is equivalent to division by zero, except where the pointers are exactly equal. This could
    // be a runtime panic, but it is simpler and safer to just disallow it (why would you want to do
    // ZST pointer arithmetic anyway?)
    #[error("pointer difference on zero-sized types is meaningless")]
    ZstPointerDifference,
    #[error("functions with #[tuple_args] must have a single argument")]
    TupleCallArgCount,
    #[error("the argument to a #[tuple_args] function must be a tuple")]
    TupleCallArgType,
    #[error("too many loop variables (iterator yields {})", .0)]
    TooManyLoopVars(String),
    #[error("too many enum variants for underlying type `{}`", .0)]
    TooManyEnumVariants(String),

    // Warnings
    #[error("protocol is used as a concrete type (did you mean to use `&dyn {}`?)", .0)]
    ProtocolsAreSpecialMkay(String),
    #[error("{} used as a concrete type, this is probably not what you want", .0)]
    InvalidTypeForValue(&'static str),
    #[error("defer inside a loop: this defered statement will only be executed once")]
    DeferInALoop,
    #[error("duplicate function name {:?} (this function will shadow a previous one)", .0)]
    DuplicateNameShadow(String),
    #[error("field `{}` is not initialized", .0)]
    UninitializedField(String),
    #[error("initializer overrides prior initialization of this union")]
    UnionInitializerOverride,
    #[error("this is `std::typing::Self`, did you mean the enclosing type?")]
    SelfConfusion,
    #[error("`#[align(1)]` has no effect, did you mean to use `#[packed]`?")]
    Align1,
    #[error("unused `{}` that must be used", .0)]
    UnusedMustUse(String),
    #[error("unused variable `{}`", .0)]
    UnusedVariable(String),
    #[error("unused closure binding `{}`", .0)]
    UnusedClosureBinding(String),
    #[error("unused parameter `{}` (prefix with `_` if required)", .0)]
    UnusedParameter(String),
    #[error("unused import `{}`", .0)]
    UnusedImport(String),
    #[error("#[{}({})] refers to a lint that does not currently exist", .0, .1)]
    ImSoMetaEvenThisAcronym(String, String),
    #[error("redundant top level block (no attributes)")]
    TopLevelBlockWithoutAttributes,
    #[error("condition is always `{}`, did you mean to use `when`?", .0)]
    ConstantCondition(bool),
    #[error("statement has no effect")]
    PureStatement,
    #[error("const-only functions should not be used at runtime (guard with `std::runtime::in_const_context()`)")]
    ConstOnly,
    #[error("this code is unreachable (dead code)")]
    DeadCode,
    #[error("pointer offset on zero-sized types is a no-op")]
    ZstPointerOffset,
    #[error("unknown attribute `{}`", .0)]
    UnknownAttribute(String),
    #[error("unnecessary cast (value is already `{}`)", .0)]
    UnnecessaryCast(String),
    #[error("loop condition is always `true` (hint: `loop {{ ... }}` is the idiomatic way of expressing infinite loops)")]
    WhileTrue,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Marker {
    Span(Span),
    Monomorphization,
    ConstEval,
    Root,
}

#[derive(Debug, Error, Clone, Hash, PartialEq, Eq)]
#[error("{}", .kind)]
pub struct CodeError {
    pub kind: CodeDiagnostic,
    pub backtrace: Vec<Marker>,
}

impl CodeError {
    pub fn from_kind(kind: CodeDiagnostic, span: Option<Span>) -> Self {
        Self {
            kind,
            backtrace: span.into_iter().map(Marker::Span).collect(),
        }
    }

    pub fn freeform(s: impl ToString) -> Self {
        Self {
            kind: CodeDiagnostic::UserDefined(s.to_string()),
            backtrace: vec![],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId {
    pub id: usize,
}

impl<'ast> AstSerializable<'ast> for FileId {
    fn serialize<W: io::Write>(
        &self,
        serializer: &mut crate::ast::serialization::AstSerializer<'ast, W>,
    ) -> crate::ast::serialization::Result<()> {
        serializer.mark_file_seen(*self);
        serializer.write_usize(self.id)
    }

    fn deserialize<R: io::Read>(
        deserializer: &mut crate::ast::serialization::AstDeserializer<'ast, R>,
    ) -> crate::ast::serialization::Result<Self> {
        let id = FileId {
            id: deserializer.read_usize()?,
        };

        Ok(deserializer.context().map_file_id(id))
    }
}

pub trait WithSpanDuringParsing<T> {
    #[allow(clippy::needless_lifetimes)]
    fn with_span_from<'ast, 'src>(
        self,
        scope: &Scope<'ast, 'src>,
        node: Node<'src>,
    ) -> Result<T, AluminaError>;
}

impl<T, E> WithSpanDuringParsing<T> for Result<T, E>
where
    CodeDiagnostic: From<E>,
{
    #[allow(clippy::needless_lifetimes)]
    fn with_span_from<'ast, 'src>(
        self,
        scope: &Scope<'ast, 'src>,
        node: Node<'src>,
    ) -> Result<T, AluminaError> {
        let span = Span::from_node(scope.code().unwrap().file_id(), node);
        self.map_err(|e| {
            AluminaError::CodeErrors(vec![CodeError {
                kind: e.into(),
                backtrace: vec![Marker::Span(span)],
            }])
        })
    }
}

pub trait CodeErrorBuilder<T> {
    fn with_no_span(self) -> Result<T, AluminaError>;
    fn with_span(self, span: Option<Span>) -> Result<T, AluminaError>;
    fn with_backtrace(self, stack: &DiagnosticsStack) -> Result<T, AluminaError>;
}

impl<T, E> CodeErrorBuilder<T> for Result<T, E>
where
    CodeDiagnostic: From<E>,
{
    fn with_no_span(self) -> Result<T, AluminaError> {
        self.map_err(|e| {
            AluminaError::CodeErrors(vec![CodeError {
                kind: e.into(),
                backtrace: vec![],
            }])
        })
    }

    fn with_span(self, span: Option<Span>) -> Result<T, AluminaError> {
        self.map_err(|e| {
            AluminaError::CodeErrors(vec![CodeError {
                kind: e.into(),
                backtrace: span.iter().map(|s| Marker::Span(*s)).collect(),
            }])
        })
    }

    fn with_backtrace(self, stack: &DiagnosticsStack) -> Result<T, AluminaError> {
        self.map_err(|e| stack.err(e.into()))
    }
}

pub struct CycleGuardian<T: Eq + Hash + Clone> {
    inner: Rc<RefCell<HashSet<T>>>,
}

pub struct CycleGuard<T: Eq + Hash + Clone> {
    guardian: Rc<RefCell<HashSet<T>>>,
    value: T,
}

impl<T: Eq + Hash + Clone> Drop for CycleGuard<T> {
    fn drop(&mut self) {
        (*self.guardian).borrow_mut().remove(&self.value);
    }
}

impl<T: Eq + Hash + Clone> CycleGuardian<T> {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(HashSet::default())),
        }
    }

    pub fn guard(&self, value: T) -> Result<CycleGuard<T>, ()> {
        if !(*self.inner).borrow_mut().insert(value.clone()) {
            return Err(());
        }

        Ok(CycleGuard {
            guardian: self.inner.clone(),
            value,
        })
    }
}

pub trait Allocatable {}

impl<T: Allocatable> Allocatable for &'_ T {}

pub trait ArenaAllocatable<'ctx, Allocator> {
    type ReturnType;

    fn alloc_on(self, allocator: &'ctx Allocator) -> Self::ReturnType;
}

macro_rules! impl_allocatable {
    ($($t:ty),*) => {
        $(
            impl crate::common::Allocatable for $t {}
        )*
    }
}

pub(crate) use impl_allocatable;

use crate::ast::lang::Lang;
use crate::ast::serialization::AstSerializable;
use crate::ast::Span;
use crate::diagnostics::DiagnosticsStack;
use crate::ir::const_eval::ConstEvalErrorKind;
use crate::src::scope::Scope;

pub trait Incrementable<T> {
    fn increment(&self) -> T;
}

macro_rules! impl_incrementable {
    ($($t:ty),*) => {
        $(
            impl Incrementable<$t> for ::std::cell::Cell<$t> {
                fn increment(&self) -> $t {
                    let old = self.get();
                    self.set(old + 1);
                    old
                }
            }
        )*
    };
}

impl_incrementable!(u8, u16, u32, u64, usize);
