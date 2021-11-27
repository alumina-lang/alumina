use std::fmt::{Debug, Display, Formatter};
use std::result::Result;
use tree_sitter::Node;

#[derive(Debug)]
pub struct SyntaxError<'syntax>(pub &'static str, pub Node<'syntax>);

impl Display for SyntaxError<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let pos = self.1.start_position();
        write!(fmt, "\"{} at {}:{}", self.0, pos.row, pos.column)
    }
}

impl std::error::Error for SyntaxError<'_> {}

#[derive(Debug)]
pub struct GenericError(pub &'static str);

impl Display for GenericError {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.0)
    }
}

impl std::error::Error for GenericError {}
