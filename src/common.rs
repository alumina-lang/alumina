use std::backtrace::Backtrace;
use std::fmt::Debug;
use std::io;
use std::result::Result;
use thiserror::Error;
use tree_sitter::Node;

#[derive(Debug, Error)]
pub enum AluminaErrorKind {
    #[error("could not resolve the path {}", .0)]
    UnresolvedPath(String),
    #[error("cycle detected while resolving names")]
    CycleDetected,
    #[error("super not allowed in this context")]
    SuperNotAllowed,
    #[error("crate not allowed in this context")]
    CrateNotAllowed,
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
    #[error("type mismatch: {} expected, {} found", .0, .1)]
    TypeMismatch(String, String),
    #[error("if branches have incompatible types ({}, {})", .0, .1)]
    MismatchedBranchTypes(String, String),
    #[error("invalid escape sequence")]
    InvalidEscapeSequence,
    #[error("cannot take address of a rvalue (yet)")]
    CannotAddressRValue,
    #[error("cannot perform {:?} between these two operands", .0)]
    InvalidBinOp(crate::ast::BinOp),
    #[error("cannot perform {:?} on operands", .0)]
    InvalidUnOp(crate::ast::UnOp),
    #[error("cannot assign to rvalue")]
    CannotAssignToRValue,
    #[error("cannot assign to const")]
    CannotAssignToConst,
    #[error("invalid cast")]
    InvalidCast,
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
    #[error("expected a struct here")]
    StructExpectedHere,
    #[error("method {:?} not found", .0)]
    MethodNotFound(String),
    #[error("duplicate enum member")]
    DuplicateEnumMember,
    #[error("cannot be called as a method")]
    NotAMethod,
    #[error("default case must be last in a switch expression")]
    DefaultCaseMustBeLast,
    #[error("cannot access {} in a nested function", .0)]
    CannotReferenceLocal(String),
    #[error("missing lang item: {:?}", .0)]
    MissingLangItem(LangItemKind),
    #[error("only slices can be range-indexed")]
    RangeIndexNonSlice,
    #[error("internal error")]
    InternalError,
}

#[derive(Debug, Error)]
pub enum AluminaError {
    #[error("{} at {:?}", .kind, .span)]
    Generic {
        kind: AluminaErrorKind,
        span: Option<Span>,
        backtrace: Backtrace, // automatically detected
    },
    #[error("{}", .source)]
    Io {
        #[from]
        source: io::Error,
    },
}
/*
impl From<AluminaErrorKind> for AluminaError {
    fn from(inner: AluminaErrorKind) -> Self {
        Self::Generic {
            kind: inner,
            span: None,
            backtrace: Backtrace::capture(),
        }
    }
}


*/

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    AluminaErrorKind: From<E>,
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

        self.map_err(|e| AluminaError::Generic {
            kind: e.into(),
            span: Some(span),
            backtrace: Backtrace::capture(),
        })
    }
}

pub trait AddSpan<T> {
    fn add_span(self, span: Option<Span>) -> Self;
}

impl<T> AddSpan<T> for Result<T, AluminaError> {
    fn add_span(self, span: Option<Span>) -> Self {
        self.map_err(|e| match e {
            AluminaError::Generic {
                kind,
                span: None,
                backtrace,
            } => AluminaError::Generic {
                kind,
                span,
                backtrace,
            },
            _ => e,
        })
    }
}

pub trait WithNoSpan<T> {
    fn with_no_span(self) -> Result<T, AluminaError>;
}

impl<T, E> WithNoSpan<T> for Result<T, E>
where
    AluminaErrorKind: From<E>,
{
    fn with_no_span(self) -> Result<T, AluminaError> {
        self.map_err(|e| AluminaError::Generic {
            kind: e.into(),
            span: None,
            backtrace: Backtrace::capture(),
        })
    }
}

pub trait WithSpan<T> {
    fn with_span(self, item: Option<Span>) -> Result<T, AluminaError>;
}

impl<T, E> WithSpan<T> for Result<T, E>
where
    AluminaErrorKind: From<E>,
{
    fn with_span(self, item: Option<Span>) -> Result<T, AluminaError> {
        self.map_err(|e| AluminaError::Generic {
            kind: e.into(),
            span: item,
            backtrace: Backtrace::capture(),
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
use crate::ast::{ExprP, Span};
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
