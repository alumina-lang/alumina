use std::fmt::Debug;
use std::result::Result;
use thiserror::Error;
use tree_sitter::Node;

#[derive(Debug, Error)]
pub enum AluminaError {
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
    #[error("type mismatch")]
    TypeMismatch,
    #[error("invalid escape sequence")]
    InvalidEscapeSequence,
    #[error("cannot take address of a rvalue (yet)")]
    CannotAddressRValue,
    #[error("cannot perform {:?} between these two operands", .0)]
    InvalidBinOp(crate::ast::BinOp),
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
}

#[derive(Debug, Error)]
#[error("{} at {}:{}", .kind, .node.start_position().row, .node.start_position().column)]
pub struct SyntaxError<'src> {
    pub kind: AluminaError,
    node: Node<'src>,
}

pub trait ToSyntaxError<T, E> {
    fn to_syntax_error<'src>(self, node: Node<'src>) -> Result<T, SyntaxError<'src>>;
}

impl<T, E> ToSyntaxError<T, E> for Result<T, E>
where
    AluminaError: From<E>,
{
    fn to_syntax_error<'src>(self, node: Node<'src>) -> Result<T, SyntaxError<'src>> {
        let a = 1usize;
        let b = 5;
        match a {
            b => {}
        }

        self.map_err(|e| SyntaxError {
            kind: e.into(),
            node,
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
