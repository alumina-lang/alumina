use std::{
    cell::{Ref, RefCell},
    fmt::{Debug, Formatter},
    rc::{Rc, Weak},
};

use crate::{
    ast::{AstId, ItemP},
    common::AluminaError,
    parser::ParseCtx,
};
use indexmap::{map::Entry, IndexMap};
use tree_sitter::Node;

use super::path::{Path, PathSegment};

#[derive(Debug, Clone)]
pub enum NamedItem<'ast, 'src> {
    Alias(Path<'src>),
    Function(ItemP<'ast>, Node<'src>, Scope<'ast, 'src>),
    Type(ItemP<'ast>, Node<'src>, Scope<'ast, 'src>),
    Module(Scope<'ast, 'src>),
    Impl(Scope<'ast, 'src>),
    Placeholder(AstId),
    Field(Node<'src>),
    Variable(AstId),
    Parameter(AstId, Node<'src>),
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
    Block,
}

pub struct ScopeInner<'ast, 'src> {
    pub r#type: ScopeType,
    pub path: Path<'src>,

    // We use IndexMap to preserve the order of items in the scope. While not important for
    // name resolution, it is important for e.g. struct layout, function signature, generic
    // parameter ordering, etc.
    pub items: IndexMap<&'src str, Vec<NamedItem<'ast, 'src>>>,
    pub parent: Option<Weak<RefCell<ScopeInner<'ast, 'src>>>>,

    code: Option<&'src ParseCtx<'src>>,
}

impl<'ast, 'src> ScopeInner<'ast, 'src> {
    pub fn all_items(&self) -> impl Iterator<Item = (&'src str, &'_ NamedItem<'ast, 'src>)> {
        self.items
            .iter()
            .flat_map(|(n, its)| its.iter().map(|i| (*n, i)))
    }

    pub fn grouped_items(&self) -> impl Iterator<Item = (&'src str, &'_ [NamedItem<'ast, 'src>])> {
        self.items.iter().map(|(n, its)| (*n, its.as_slice()))
    }

    pub fn items_with_name(&self, name: &str) -> impl Iterator<Item = &NamedItem<'ast, 'src>> {
        self.items.get(name).into_iter().flat_map(|its| its.iter())
    }
}

impl<'ast, 'src> Debug for ScopeInner<'ast, 'src> {
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
pub struct Scope<'ast, 'src>(pub Rc<RefCell<ScopeInner<'ast, 'src>>>);

impl<'ast, 'src> From<Scope<'ast, 'src>> for Weak<RefCell<ScopeInner<'ast, 'src>>> {
    fn from(scope: Scope<'ast, 'src>) -> Self {
        Rc::downgrade(&scope.0)
    }
}

impl<'ast, 'src> Debug for Scope<'ast, 'src> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.inner().fmt(fmt)
    }
}

impl<'ast, 'src> Scope<'ast, 'src> {
    pub fn new_root() -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type: ScopeType::Root,
            path: Path::root(),
            items: IndexMap::new(),
            parent: None,
            code: None,
        })))
    }

    pub fn inner(&self) -> Ref<'_, ScopeInner<'ast, 'src>> {
        self.0.borrow()
    }

    pub fn code(&self) -> Option<&'src ParseCtx<'src>> {
        self.inner().code.clone()
    }

    pub fn path(&self) -> Path<'src> {
        self.inner().path.clone()
    }

    pub fn named_child(&self, r#type: ScopeType, name: &'src str) -> Self {
        let new_path = self.0.borrow().path.extend(PathSegment(name));

        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: new_path,
            items: IndexMap::new(),
            code: self.code(),
            parent: Some(Rc::downgrade(&self.0)),
        })))
    }

    pub fn anonymous_child(&self, r#type: ScopeType) -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: self.path(),
            items: IndexMap::new(),
            code: self.code(),
            parent: Some(Rc::downgrade(&self.0)),
        })))
    }

    pub fn named_child_with_ctx(
        &self,
        r#type: ScopeType,
        name: &'src str,
        code: &'src ParseCtx<'src>,
    ) -> Self {
        let new_path = self.inner().path.extend(PathSegment(name));
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: new_path,
            items: IndexMap::new(),
            parent: Some(Rc::downgrade(&self.0)),
            code: Some(code),
        })))
    }

    pub fn add_item(
        &self,
        name: &'src str,
        item: NamedItem<'ast, 'src>,
    ) -> Result<(), AluminaError> {
        let mut current_scope = self.0.borrow_mut();
        let scope_type = current_scope.r#type;

        // Duplicate names are generally not allowed, but we allow them for
        // types and their impls.
        match current_scope.items.entry(name) {
            Entry::Vacant(entry) => {
                entry.insert(vec![item]);
                return Ok(());
            }
            Entry::Occupied(mut entry) => {
                let existing = entry.get_mut();
                if let ScopeType::Block = scope_type {
                    // In linear scopes we allow shadowing.
                    existing[0] = item;
                    return Ok(());
                } else if existing.len() == 1
                    && ((matches!(existing[0], NamedItem::Type(_, _, _))
                        && matches!(item, NamedItem::Impl(_)))
                        || (matches!(existing[0], NamedItem::Impl(_))
                            && matches!(item, NamedItem::Type(_, _, _))))
                {
                    existing.push(item);
                    existing.sort_by_key(|i| match i {
                        NamedItem::Type(_, _, _) => 0,
                        NamedItem::Impl(_) => 1,
                        _ => unreachable!(),
                    });
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
            ScopeType::Module => self.parent(),
            _ => self.parent().and_then(|p| p.find_super()),
        }
    }

    pub fn parent(&self) -> Option<Self> {
        self.inner()
            .parent
            .as_ref()
            .map(|parent| Self(parent.upgrade().unwrap()))
    }
}
