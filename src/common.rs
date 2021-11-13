use std::fmt::{Debug, Display, Formatter};
use std::result::Result;
use tree_sitter::Node;

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum GenericArg<'a> {
    Placeholder(&'a str),
    Type(Path<'a>),
}

impl<'syntax> Display for GenericArg<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            GenericArg::Placeholder(s) => write!(fmt, "{}", s),
            GenericArg::Type(fqn) => write!(fmt, "{}", fqn),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PathSegment<'syntax> {
    Ident(&'syntax str),
    Generics(Vec<GenericArg<'syntax>>),
}

impl<'syntax> Display for PathSegment<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            PathSegment::Ident(s) => write!(fmt, "{}", s),
            PathSegment::Generics(args) => {
                write!(fmt, "<")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}", arg)?;
                }
                write!(fmt, ">")
            }
        }
    }
}

#[derive(Default, PartialEq, Eq, Hash, Clone)]
pub struct Path<'syntax> {
    pub absolute: bool,
    pub segments: Vec<PathSegment<'syntax>>,
}

impl<'syntax> Display for Path<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        for (i, seg) in self.segments.iter().enumerate() {
            if i > 0 || self.absolute {
                write!(fmt, "::")?;
            }
            write!(fmt, "{}", seg)?;
        }
        Ok(())
    }
}

impl<'syntax> Debug for Path<'syntax> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        Display::fmt(self, fmt)
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
