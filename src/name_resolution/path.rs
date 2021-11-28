use std::fmt::{Debug, Display, Formatter};

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PathSegment<'src>(pub &'src str);

impl<'src> Display for PathSegment<'src> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.0)
    }
}

#[derive(Default, PartialEq, Eq, Hash, Clone)]
pub struct Path<'src> {
    pub absolute: bool,
    pub segments: Vec<PathSegment<'src>>,
}

impl<'src> Display for Path<'src> {
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

impl<'src> Debug for Path<'src> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "\"{}\"", self)
    }
}

impl<'src> From<PathSegment<'src>> for Path<'src> {
    fn from(item: PathSegment<'src>) -> Self {
        Self {
            absolute: false,
            segments: vec![item],
        }
    }
}

impl<'src> Path<'src> {
    pub fn root() -> Self {
        Self {
            absolute: true,
            segments: vec![],
        }
    }

    pub fn extend(&self, part: PathSegment<'src>) -> Self {
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

    pub fn join_with(&self, lhs: Path<'src>) -> Self {
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
