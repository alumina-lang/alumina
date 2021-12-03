use std::fmt::Debug;
use std::result::Result;
use thiserror::Error;
use tree_sitter::Node;

#[derive(Debug, Error)]
pub enum AluminaError {
    #[error("could not resolve the path")]
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
        self.map_err(|e| SyntaxError {
            kind: e.into(),
            node,
        })
    }
}

pub trait Allocatable {}

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
