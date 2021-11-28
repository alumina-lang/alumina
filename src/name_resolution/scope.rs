use std::{
    cell::RefCell,
    fmt::{Debug, Formatter},
    rc::{Rc, Weak},
};

use crate::{common::AluminaError, parser::ParseCtx, types::SymbolP};
use indexmap::{map::Entry, IndexMap};
use tree_sitter::Node;

use super::path::{Path, PathSegment};

#[derive(Debug, Clone)]
pub enum Item<'gcx, 'src> {
    Function(SymbolP<'gcx>, Node<'src>, Scope<'gcx, 'src>),
    Type(SymbolP<'gcx>, Node<'src>, Scope<'gcx, 'src>),
    Module(Scope<'gcx, 'src>),
    Impl(Scope<'gcx, 'src>),
    Placeholder(SymbolP<'gcx>),
    Field(SymbolP<'gcx>, Node<'src>),
    Alias(Path<'src>),
}

#[derive(Debug, Copy, Clone)]
pub enum ScopeType {
    Root,
    Crate,
    Module,
    Struct,
    Function,
    Impl,
    Enum,
}

pub struct ScopeInner<'gcx, 'src> {
    pub r#type: ScopeType,
    pub path: Path<'src>,

    // We use IndexMap to preserve the order of items in the scope. While not important for
    // name resolution, it is important for e.g. struct layout, function signature, generic
    // parameter ordering, etc.
    pub items: IndexMap<&'src str, Vec<Item<'gcx, 'src>>>,
    pub parent: Option<Weak<RefCell<ScopeInner<'gcx, 'src>>>>,

    parse_context: Option<ParseCtx<'gcx, 'src>>,
}

impl<'gcx, 'src> Debug for ScopeInner<'gcx, 'src> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), std::fmt::Error> {
        let mut builder = fmt.debug_struct(&format!("{:?}Scope({:?})", self.r#type, self.path));
        for (name, items) in &self.items {
            for item in items {
                builder.field(name, item);
            }
        }
        builder.finish()
    }
}

#[derive(Clone)]
pub struct Scope<'gcx, 'src>(pub Rc<RefCell<ScopeInner<'gcx, 'src>>>);

impl<'gcx, 'src> From<Scope<'gcx, 'src>> for Weak<RefCell<ScopeInner<'gcx, 'src>>> {
    fn from(scope: Scope<'gcx, 'src>) -> Self {
        Rc::downgrade(&scope.0)
    }
}

impl<'gcx, 'src> Debug for Scope<'gcx, 'src> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.borrow().fmt(fmt)
    }
}

impl<'gcx, 'src> Scope<'gcx, 'src> {
    pub fn new_root() -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type: ScopeType::Root,
            path: Path::root(),
            items: IndexMap::new(),
            parent: None,
            parse_context: None,
        })))
    }

    pub fn parse_ctx(&self) -> Option<ParseCtx<'gcx, 'src>> {
        self.0.borrow().parse_context.clone()
    }

    pub fn with_parent(r#type: ScopeType, path: Path<'src>, parent: Scope<'gcx, 'src>) -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path,
            items: IndexMap::new(),
            parse_context: parent.parse_ctx(),
            parent: Some(parent.into()),
        })))
    }

    pub fn r#type(&self) -> ScopeType {
        self.0.borrow().r#type
    }

    pub fn path(&self) -> Path<'src> {
        self.0.borrow().path.clone()
    }

    pub fn new_child(&self, r#type: ScopeType, name: &'src str) -> Self {
        let new_path = self.0.borrow().path.extend(PathSegment(name));
        Scope::with_parent(r#type, new_path, self.clone())
    }

    pub fn new_child_with_parse_ctx(
        &self,
        r#type: ScopeType,
        name: &'src str,
        parse_ctx: ParseCtx<'gcx, 'src>,
    ) -> Self {
        let new_path = self.0.borrow().path.extend(PathSegment(name));
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: new_path,
            items: IndexMap::new(),
            parent: Some(Rc::downgrade(&self.0)),
            parse_context: Some(parse_ctx),
        })))
    }

    pub fn add_item(&self, name: &'src str, item: Item<'gcx, 'src>) -> Result<(), AluminaError> {
        let mut current_scope = self.0.borrow_mut();

        // Duplicate names are generally not allowed, but we allow them for
        // types and their impls.
        match current_scope.items.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(vec![item]);
                return Ok(());
            }
            Entry::Occupied(mut entry) => {
                let existing = entry.get_mut();
                if existing.len() == 1
                    && ((matches!(existing[0], Item::Type(_, _, _))
                        && matches!(item, Item::Impl(_)))
                        || (matches!(existing[0], Item::Impl(_))
                            && matches!(item, Item::Type(_, _, _))))
                {
                    existing.push(item);
                    return Ok(());
                }
            }
        }

        Err(AluminaError::DuplicateName(name.into()))
    }

    pub fn find_root(&self) -> Self {
        let mut current = self.clone();
        while let Some(parent) = current.parent() {
            current = parent;
        }
        current
    }

    pub fn find_crate(&self) -> Option<Self> {
        let mut current = self.clone();

        loop {
            let r#type = current.0.borrow().r#type;
            if let ScopeType::Crate = r#type {
                return Some(current);
            }

            if let Some(parent) = current.parent() {
                current = parent;
            } else {
                break;
            }
        }

        None
    }

    pub fn find_super(&self) -> Option<Self> {
        // Function, struct, enum, ... are transparently scoped to their parent
        match self.0.borrow().r#type {
            ScopeType::Root | ScopeType::Crate => None,
            ScopeType::Module | ScopeType::Impl => self.parent(),
            _ => self.parent().and_then(|p| p.find_super()),
        }
    }

    pub fn parent(&self) -> Option<Self> {
        self.0
            .borrow()
            .parent
            .as_ref()
            .map(|parent| Self(parent.upgrade().unwrap()))
    }
}
