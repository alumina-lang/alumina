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
