use std::fmt::{Debug, Display, Formatter, write};
use std::result::Result;
use tree_sitter::Node;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PathSegment<'syntax>(pub &'syntax str);

impl<'syntax> Display for PathSegment<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.0)
    }
}

#[derive(Default, PartialEq, Eq, Hash, Clone)]
pub struct Path<'syntax> {
    pub absolute: bool,
    pub segments: Vec<PathSegment<'syntax>>,
}

impl<'syntax> Display for Path<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.absolute {
            write!(fmt, "::")?;
        }
        for (i, seg) in self.segments.iter().enumerate() {
            if i > 0 {
                write!(fmt, "::")?;
            }
            write!(fmt, "{}", seg)?;
        }
        Ok(())
    }
}

impl<'syntax> Debug for Path<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "\"{}\"", self)
    }
}

impl<'syntax> From<PathSegment<'syntax>> for Path<'syntax> {
    fn from(item: PathSegment<'syntax>) -> Self {
        Self {
            absolute: false,
            segments: vec![item],
        }
    }
}

impl<'syntax> Path<'syntax> {
    pub fn root() -> Self {
        Self {
            absolute: true,
            segments: vec![],
        }
    }

    pub fn extend(&self, part: PathSegment<'syntax>) -> Self {
        Self {
            absolute: self.absolute,
            segments: self
                .segments
                .iter()
                .cloned()
                .chain(std::iter::once(part))
                .collect(),
        }
    }

    pub fn join_with(&self, lhs: Path<'syntax>) -> Self {
        assert!(!lhs.absolute || self.absolute || self.segments.is_empty());

        Self {
            absolute: lhs.absolute || self.absolute,
            segments: self.segments.iter().cloned().chain(lhs.segments).collect(),
        }
    }

    pub fn pop(&self) -> Self {
        Self {
            absolute: self.absolute,
            segments: self.segments[..self.segments.len() - 1].to_vec(),
        }
    }
}

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
