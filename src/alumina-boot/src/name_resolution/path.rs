use std::fmt::{Debug, Display, Formatter};

use alumina_boot_macros::AstSerializable;

#[derive(Debug, PartialEq, Eq, Hash, Clone, AstSerializable)]
pub struct PathSegment<'ast>(pub &'ast str);

impl<'ast> Display for PathSegment<'ast> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.0)
    }
}

#[derive(Default, PartialEq, Eq, Hash, Clone, Debug, AstSerializable)]
pub struct Path<'ast> {
    pub absolute: bool,
    pub segments: Vec<PathSegment<'ast>>,
}

impl<'ast> Display for Path<'ast> {
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

impl<'ast> From<PathSegment<'ast>> for Path<'ast> {
    fn from(item: PathSegment<'ast>) -> Self {
        Self {
            absolute: false,
            segments: vec![item],
        }
    }
}

impl<'ast> Path<'ast> {
    pub fn root() -> Self {
        Self {
            absolute: true,
            segments: vec![],
        }
    }

    pub fn extend(&self, part: PathSegment<'ast>) -> Self {
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

    pub fn join_with(&self, lhs: Path<'ast>) -> Self {
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

    pub fn is_root(&self) -> bool {
        self.segments.is_empty() && self.absolute
    }
}
