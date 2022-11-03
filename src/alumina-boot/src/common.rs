use std::cell::RefCell;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::io;
use std::rc::Rc;
use std::result::Result;
use strum_macros::{AsRefStr, EnumVariantNames};
use thiserror::Error;
use tree_sitter::Node;

macro_rules! ice {
    ($why:literal) => {{
        use crate::common::CodeErrorBuilder;
        return Err(CodeErrorKind::InternalError(
            $why.to_string(),
            backtrace::Backtrace::new().into(),
        ))
        .with_no_span();
    }};
}

pub(crate) use ice;

pub type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;
pub type HashSet<T> = rustc_hash::FxHashSet<T>;
pub type IndexMap<K, V> =
    indexmap::IndexMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
pub type IndexSet<K> = indexmap::IndexSet<K, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

/// Newtype wrapper for non-comparable subobjects where it does not matter
pub struct ExcludeFromEq<T>(pub T);
impl<T> Hash for ExcludeFromEq<T> {
    fn hash<H: Hasher>(&self, _state: &mut H) {}
}
impl<T> PartialEq for ExcludeFromEq<T> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl<T> Eq for ExcludeFromEq<T> {}
impl<T: Debug> Debug for ExcludeFromEq<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl<T> From<T> for ExcludeFromEq<T> {
    fn from(t: T) -> Self {
        Self(t)
    }
}
impl<T: Clone> Clone for ExcludeFromEq<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<T: Copy> Copy for ExcludeFromEq<T> {}

#[derive(Debug, Error)]
pub enum AluminaError {
    #[error("code errors: {0:?}")]
    CodeErrors(Vec<CodeError>),
    #[error("io error: {0}")]
    Io(#[from] io::Error),
    #[error("{0}")]
    WalkDir(#[from] walkdir::Error),
}

// thiserror uses string matching in its proc macro and assumes that "Backtrace" is
// "std::backtrace::Backtrace", which is unstable.
use backtrace::Backtrace as NonStdBacktrace;

/// Main enum for all errors and warnings that can occur during compilation
#[derive(AsRefStr, EnumVariantNames, Debug, Error, Clone, Hash, PartialEq, Eq)]
#[strum(serialize_all = "snake_case")]
pub enum CodeErrorKind {
    // Errors
    #[error("syntax error: unexpected `{}`", .0)]
    ParseError(String),
    #[error("unexpected `{}` here", .0)]
    Unexpected(String),
    #[error("could not resolve the path `{}`", .0)]
    UnresolvedPath(String),
    #[error("cycle detected while resolving aliases")]
    CycleDetected,
    #[error("duplicate name `{}`", .0)]
    DuplicateName(String),
    #[error("duplicate name `{}` ({} cannot shadow a {})", .0, .1, .2)]
    CannotShadow(String, String, String),
    #[error("generic associated types are not supported, soz")]
    NoAssociatedTypes,
    #[error("invalid literal")]
    InvalidLiteral,
    #[error("character literals must be exactly one byte")]
    InvalidCharLiteral,
    #[error("{} generic parameters expected, {} found" , .0, .1)]
    GenericParamCountMismatch(usize, usize),
    #[error("type expected here")]
    TypeExpectedHere,
    #[error("only enums and structs can have generic parameters")]
    UnexpectedGenericParams,
    #[error("type is recursive without indirection")]
    RecursiveWithoutIndirection,
    #[error("type hint required")]
    TypeHintRequired,
    // This is a separate error type so that it can be filtered out during failed tentative
    // monomorphization
    #[error("type hint required (type inference)")]
    TypeInferenceFailed,
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
    #[error("could not resolve item `{}`", .0)]
    UnresolvedItem(String),
    #[error("duplicate field `{}` in struct initializer", .0)]
    DuplicateFieldInitializer(String),
    #[error("expected a struct-like type here")]
    StructLikeExpectedHere,
    #[error("method `{}` not found on `{}`", .0, .1)]
    MethodNotFound(String, String),
    #[error("duplicate enum member")]
    DuplicateEnumMember,
    #[error("cannot be called as a method")]
    NotAMethod,
    #[error("default case must be last in a switch expression")]
    DefaultCaseMustBeLast,
    #[error("cannot reference `{}` in a nested function", .0)]
    CannotReferenceLocal(String),
    #[error("local items cannot bind ambient generic placeholders (yet)")]
    LocalItemsCannotBindGenericPlaceholders,
    #[error("missing lang item: {:?}", .0)]
    MissingLangItem(LangItemKind),
    #[error("only slices can be range-indexed")]
    RangeIndexNonSlice,
    #[error("internal error: {}", .0)]
    InternalError(String, ExcludeFromEq<NonStdBacktrace>),
    // This error is a compiler bug if it happens on its own, but it can pop up when
    // we abort early due to a previous error.
    #[error("local with unknown type")]
    LocalWithUnknownType,
    #[error("unsupported ABI {:?}", .0)]
    UnsupportedABI(String),
    #[error("unknown intrinsic `{}`", .0)]
    UnknownIntrinsic(String),
    #[error("unknown lang item {:?}", .0)]
    UnknownLangItem(Option<String>),
    #[error("this cannot be a lang item")]
    CannotBeALangItem,
    #[error("cannot take address of a compiler intrinsic")]
    IntrinsicsAreSpecialMkay,
    #[error("extern \"C\" functions cannot have generic parameters")]
    ExternCGenericParams,
    #[error("constant string expected")]
    ConstantStringExpected,
    #[error("this expression is not evaluable at compile time ({})", .0)]
    CannotConstEvaluate(ConstEvalError),
    #[error("values of enum variants can only be integers")]
    InvalidValueForEnumVariant,
    #[error("{}", .0)]
    UserDefined(String),
    #[error("cannot defer inside a defered expression")]
    DeferInDefer,
    #[error("`...` expressions can only be used in macros")]
    EtCeteraOutsideOfMacro,
    #[error("`$` identifiers can only be used in macros")]
    DollaredOutsideOfMacro,
    #[error("this macro does not have any `...` arguments")]
    NoEtCeteraArgs,
    #[error("macro can have at most one `...` parameter")]
    MultipleEtCeteras,
    #[error("recursive macro calls are not allowed")]
    RecursiveMacroCall,
    #[error("`{}` is not a macro", .0)]
    NotAMacro(String),
    #[error("not enough macro arguments, at least {} expected", .0)]
    NotEnoughMacroArguments(usize),
    #[error("nested `...` expansions are not supported (yet)")]
    EtCeteraInEtCetera,
    #[error("`...` expansion is not allowed in this position")]
    CannotEtCeteraHere,
    #[error("`{}` is a macro (hint: append `!`)", .0)]
    IsAMacro(String),
    #[error("cyclic dependency during static initialization")]
    RecursiveStaticInitialization,
    #[error("can only do that in function scope")]
    NotInAFunctionScope,
    #[error("unknown builtin macro `{}`", .0)]
    UnknownBuiltinMacro(String),
    #[error("`{}` is not a protocol", .0)]
    NotAProtocol(String),
    #[error("protocol is not expected here")]
    UnexpectedProtocol,
    #[error("function must have a body")]
    FunctionMustHaveBody,
    #[error("protocol functions cannot be extern")]
    ProtocolFnsCannotBeExtern,
    #[error("varargs functions can only be extern")]
    VarArgsCanOnlyBeExtern,
    #[error("type `{}` matches `{}`, which it should not", .0, .1)]
    ProtocolMatch(String, String),
    #[error("type `{}` does not match `{}`", .0, .1)]
    ProtocolMismatch(String, String),
    #[error("type `{}` does not match `{}` ({})", .0, .1, .2)]
    ProtocolMismatchDetail(String, String, String),
    #[error("recursive protocol bounds are not supported")]
    CyclicProtocolBound,
    #[error("unimplemented: {}", .0)]
    Unimplemented(String),
    #[error("multiple `main` functions found")]
    MultipleMainFunctions,
    #[error("type aliases cannot have their own impl block")]
    NoImplForTypedefs,
    #[error("unpopulated symbol")]
    UnpopulatedSymbol,
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
    #[error("thread local storage is not supported")]
    ThreadLocalNotSupported,
    #[error("dyn requires a protocol")]
    NonProtocolDyn,
    #[error("builtin protocols cannot be used with `dyn`")]
    BuiltinProtocolDyn,
    #[error("protocols containing generic functions can only be used as mixins")]
    MixinOnlyProtocol,
    #[error("protocols cannot be used as concrete types (did you mean to use `&dyn {}`?)", .0)]
    ProtocolsAreSpecialMkay(String),
    #[error("indirect `dyn` pointers are not supported")]
    IndirectDyn,
    #[error("`{}` cannot be used as a concrete type", .0)]
    SpecialNamedType(String),
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
    #[error(
        "`#[align(...)]` cannot be used together with `#[packed]` (alignment will always be 1)"
    )]
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

    // Warnings
    #[error("defer inside a loop: this defered statement will only be executed once")]
    DeferInALoop,
    #[error("duplicate function name {:?} (this function will shadow a previous one)", .0)]
    DuplicateNameShadow(String),
    #[error("field `{}` is not initialized", .0)]
    UninitializedField(String),
    #[error("This is `std::typing::Self`, did you mean the enclosing type?")]
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
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Marker {
    Span(Span),
    Monomorphization,
}

#[derive(Debug, Error, Clone, Hash, PartialEq, Eq)]
#[error("{}", .kind)]
pub struct CodeError {
    pub kind: CodeErrorKind,
    pub backtrace: Vec<Marker>,
    //pub code_backtrace: Backtrace,
}

impl CodeError {
    pub fn from_kind(kind: CodeErrorKind, span: Option<Span>) -> Self {
        Self {
            kind,
            backtrace: span.into_iter().map(Marker::Span).collect(),
        }
    }

    pub fn freeform(s: impl ToString) -> Self {
        Self {
            kind: CodeErrorKind::UserDefined(s.to_string()),
            backtrace: vec![],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId {
    pub id: usize,
}

pub trait WithSpanDuringParsing<T> {
    fn with_span_from<'ast, 'src>(
        self,
        scope: &Scope<'ast, 'src>,
        node: Node<'src>,
    ) -> Result<T, AluminaError>;
}

impl<T, E> WithSpanDuringParsing<T> for Result<T, E>
where
    CodeErrorKind: From<E>,
{
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

pub trait CodeErrorBacktrace<T> {
    fn append_span(self, span: Option<Span>) -> Self;
    fn append_mono_marker(self) -> Self;
}

impl<T> CodeErrorBacktrace<T> for Result<T, AluminaError> {
    fn append_span(self, span: Option<Span>) -> Self {
        self.map_err(|mut e| match &mut e {
            AluminaError::CodeErrors(errors) => {
                for error in errors {
                    error
                        .backtrace
                        .extend(span.iter().map(|s| Marker::Span(*s)));
                }
                e
            }
            _ => e,
        })
    }

    fn append_mono_marker(self) -> Self {
        self.map_err(|mut e| match &mut e {
            AluminaError::CodeErrors(errors) => {
                for error in errors {
                    error.backtrace.push(Marker::Monomorphization);
                }
                e
            }
            _ => e,
        })
    }
}

pub trait CodeErrorBuilder<T> {
    fn with_no_span(self) -> Result<T, AluminaError>;
    fn with_span(self, span: Option<Span>) -> Result<T, AluminaError>;
}

impl<T, E> CodeErrorBuilder<T> for Result<T, E>
where
    CodeErrorKind: From<E>,
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

use crate::ast::lang::LangItemKind;
use crate::ast::Span;
use crate::ir::const_eval::ConstEvalError;
use crate::name_resolution::scope::Scope;

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
