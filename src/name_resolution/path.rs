use std::fmt::{Debug, Display, Formatter};

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
