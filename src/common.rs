use std::backtrace::Backtrace;
use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::io;
use std::rc::Rc;
use std::result::Result;
use thiserror::Error;
use tree_sitter::Node;

macro_rules! ice {
    ($why:literal) => {
        return Err(CodeErrorKind::InternalError(
            $why.to_string(),
            std::rc::Rc::new(std::backtrace::Backtrace::capture()),
        ))
        .with_no_span()
    };
}

pub(crate) use ice;

#[derive(Debug, Error)]
pub enum AluminaError {
    #[error("code errors: {0:?}")]
    CodeErrors(Vec<CodeError>),
    #[error("io error: {0}")]
    Io(#[from] io::Error),
    #[error("{0}")]
    WalkDir(#[from] walkdir::Error),
}

#[derive(Debug, Error, Clone)]
pub enum CodeErrorKind {
    // Errors
    #[error("syntax error: unexpected {:?}", .0)]
    ParseError(String),

    #[error("unexpected {:?} here", .0)]
    Unexpected(String),
    #[error("could not resolve the path {}", .0)]
    UnresolvedPath(String),
    #[error("cycle detected while resolving aliases")]
    CycleDetected,
    #[error("super not allowed in this context")]
    SuperNotAllowed,
    #[error("duplicate name {:?}", .0)]
    DuplicateName(String),
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
    #[error("type mismatch: {} expected, {} found", .0, .1)]
    TypeMismatch(String, String),
    #[error("branches have incompatible types ({}, {})", .0, .1)]
    MismatchedBranchTypes(String, String),
    #[error("invalid escape sequence")]
    InvalidEscapeSequence,
    #[error("cannot take address of a rvalue (yet)")]
    CannotAddressRValue,
    #[error("cannot perform {:?} between {} and {}", .0, .1, .2)]
    InvalidBinOp(crate::ast::BinOp, String, String),
    #[error("cannot perform {:?} on {}", .0, .1)]
    InvalidUnOp(crate::ast::UnOp, String),
    #[error("cannot assign to rvalue")]
    CannotAssignToRValue,
    #[error("cannot assign to const")]
    CannotAssignToConst,
    #[error("cannot cast {} into {}", .0, .1)]
    InvalidCast(String, String),
    #[error("break outside of loop")]
    BreakOutsideOfLoop,
    #[error("continue outside of loop")]
    ContinueOutsideOfLoop,
    #[error("expected {} arguments, found {}", .0, .1)]
    ParamCountMismatch(usize, usize),
    #[error("tuple index out of bounds")]
    TupleIndexOutOfBounds,
    #[error("function expected")]
    FunctionExpectedHere,
    #[error("could not resolve item {:?}", .0)]
    UnresolvedItem(String),
    #[error("duplicate field {:?} in struct initializer", .0)]
    DuplicateFieldInitializer(String),
    #[error("expected a struct-like type here")]
    StructLikeExpectedHere,
    #[error("method {} not found", .0)]
    MethodNotFound(String),
    #[error("duplicate enum member")]
    DuplicateEnumMember,
    #[error("cannot be called as a method")]
    NotAMethod,
    #[error("default case must be last in a switch expression")]
    DefaultCaseMustBeLast,
    #[error("cannot reference {:?} in a nested function", .0)]
    CannotReferenceLocal(String),
    #[error("missing lang item: {:?}", .0)]
    MissingLangItem(LangItemKind),
    #[error("only slices can be range-indexed")]
    RangeIndexNonSlice,
    #[error("internal error: {}", .0)]
    InternalError(String, Rc<Backtrace>),
    // This error is a compiler bug if it happens on its own, but it can pop up when
    // we abort early due to a previous error.
    #[error("local with unknown type")]
    LocalWithUnknownType,
    #[error("unsupported ABI {}", .0)]
    UnsupportedABI(String),
    #[error("unknown intrinsic {}", .0)]
    UnknownIntrinsic(String),
    #[error("unknown lang item {:?}", .0)]
    UnknownLangItem(Option<String>),
    #[error("this cannot be a lang item")]
    CannotBeALangItem,
    #[error("cannot take address of a compiler intrinsic")]
    IntrinsicsAreSpecialMkay,
    #[error("extern \"C\" functions cannot have generic parameters")]
    ExternCGenericParams,
    #[error("this expression is not evaluable at compile time")]
    CannotConstEvaluate,
    #[error("invalid value for enum variant")]
    InvalidValueForEnumVariant,
    #[error("{}", .0)]
    ExplicitCompileFail(String),
    #[error("cannot defer inside a defered expression")]
    DeferInDefer,
    #[error("`...` expressions can only be used in macros")]
    EtCeteraOutsideOfMacro,
    #[error("this macro does not have any `...` arguments")]
    NoEtCeteraArgs,
    #[error("macro can have at most one `...` parameter")]
    MultipleEtCeteras,
    #[error("recursive macro calls are not allowed")]
    RecursiveMacroCall,
    #[error("{} is not a macro", .0)]
    NotAMacro(String),
    #[error("not enough macro arguments, at least {} expected", .0)]
    NotEnoughMacroArguments(usize),
    #[error("nested `...` expansions are not supported (yet)")]
    EtCeteraInEtCetera,
    #[error("`...` expansion is not allowed in this position")]
    CannotEtCeteraHere,
    #[error("{} is a macro (hint: append `!`)", .0)]
    IsAMacro(String),
    #[error("cyclic dependency during static initialization")]
    RecursiveStaticInitialization,
    #[error("can only do that in function scope")]
    NotInAFunctionScope,
    #[error("unknown builtin macro {}", .0)]
    UnknownBuiltinMacro(String),
    #[error("{} is not a protocol", .0)]
    NotAProtocol(String),
    #[error("protocol is not expected here")]
    UnexpectedProtocol,
    #[error("function must have a body")]
    FunctionMustHaveBody,
    #[error("protocol functions cannot be generic (hint: move the generic parameters to the protocol itself)")]
    ProtocolFnsCannotBeGeneric,
    #[error("protocol functions cannot be extern")]
    ProtocolFnsCannotBeExtern,
    #[error("type parameter {} matches {}, which it should not", .0, .1)]
    ProtocolMatch(String, String),
    #[error("type parameter {} does not match {}", .0, .1)]
    ProtocolMismatch(String, String),
    #[error("type parameter {} does not match {} ({})", .0, .1, .2)]
    ProtocolMismatchDetail(String, String, String),
    #[error("recursive protocol bounds are not supported")]
    CyclicProtocolBound,
    #[error("unimplemented: {}", .0)]
    Unimplemented(String),
    #[error("type aliases cannot have their own impl block")]
    NoImplForTypedefs,
    #[error("unpopulated symbol")]
    UnpopulatedSymbol,
    #[error(
        "generic type parameters cannot be used in this context (did you mean to call a function?)"
    )]
    GenericArgsInPath,

    #[error("cannot determine source span")]
    NoSpanInformation,
    #[error("cannot have an `impl` block without a corresponding type")]
    NoFreeStandingImpl,

    // Warnings
    #[error("defer inside a loop: this defered statement will only be executed once")]
    DeferInALoop,
    #[error("duplicate function name {:?} (this function will shadow a previous one)", .0)]
    DuplicateNameShadow(String),
}

#[derive(Debug, Clone)]
pub enum Marker {
    Span(Span),
    Monomorphization,
}

#[derive(Debug, Error, Clone)]
#[error("{}", .kind)]
pub struct CodeError {
    pub kind: CodeErrorKind,
    pub backtrace: Vec<Marker>,
    //pub code_backtrace: Backtrace,
}

impl CodeError {
    pub fn from_kind(kind: CodeErrorKind, span: Span) -> Self {
        Self {
            kind,
            backtrace: vec![Marker::Span(span)],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId {
    pub id: usize,
}

pub trait WithSpanDuringParsing<T> {
    fn with_span<'ast, 'src>(
        self,
        scope: &Scope<'ast, 'src>,
        node: Node<'src>,
    ) -> Result<T, AluminaError>;
}

impl<T, E> WithSpanDuringParsing<T> for Result<T, E>
where
    CodeErrorKind: From<E>,
{
    fn with_span<'ast, 'src>(
        self,
        scope: &Scope<'ast, 'src>,
        node: Node<'src>,
    ) -> Result<T, AluminaError> {
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

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
            inner: Rc::new(RefCell::new(HashSet::new())),
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
