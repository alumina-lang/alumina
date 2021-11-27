use std::{
    cell::RefCell,
    collections::{hash_map::Entry, HashMap},
    fmt::{Debug, Formatter},
    rc::{Rc, Weak},
};

use crate::{common::GenericError, types::SymbolP};
use tree_sitter::Node;

use super::path::{Path, PathSegment};

#[derive(Debug, Clone)]
pub enum Item<'tcx> {
    Function(SymbolP<'tcx>, Node<'tcx>, Scope<'tcx>),
    Type(SymbolP<'tcx>, Node<'tcx>, Scope<'tcx>),
    Module(Scope<'tcx>),
    Impl(Scope<'tcx>),
    Placeholder(SymbolP<'tcx>),
    Field(SymbolP<'tcx>, Node<'tcx>),
    Alias(Path<'tcx>),
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

pub struct ScopeInner<'tcx> {
    pub r#type: ScopeType,
    pub path: Path<'tcx>,
    pub items: HashMap<&'tcx str, Vec<Item<'tcx>>>,
    pub parent: Option<Weak<RefCell<ScopeInner<'tcx>>>>,
}

impl<'tcx> Debug for ScopeInner<'tcx> {
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
pub struct Scope<'tcx>(pub Rc<RefCell<ScopeInner<'tcx>>>);

impl<'tcx> From<Scope<'tcx>> for Weak<RefCell<ScopeInner<'tcx>>> {
    fn from(scope: Scope<'tcx>) -> Self {
        Rc::downgrade(&scope.0)
    }
}

impl<'tcx> Debug for Scope<'tcx> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.borrow().fmt(fmt)
    }
}

impl<'tcx> Scope<'tcx> {
    pub fn new() -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type: ScopeType::Root,
            path: Path::root(),
            items: HashMap::new(),
            parent: None,
        })))
    }

    pub fn with_parent(r#type: ScopeType, path: Path<'tcx>, parent: Scope<'tcx>) -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path,
            items: HashMap::new(),
            parent: Some(parent.into()),
        })))
    }

    pub fn r#type(&self) -> ScopeType {
        self.0.borrow().r#type
    }

    pub fn path(&self) -> Path<'tcx> {
        self.0.borrow().path.clone()
    }

    pub fn make_child(&self, r#type: ScopeType, name: &'tcx str) -> Self {
        let new_path = self.0.borrow().path.extend(PathSegment(name));
        Scope::with_parent(r#type, new_path, self.clone())
    }

    pub fn add_item(&self, name: &'tcx str, item: Item<'tcx>) -> Result<(), GenericError> {
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

        Err(GenericError("duplicate item"))
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
