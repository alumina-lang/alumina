use crate::ast::{Attribute, Id, ItemP, Span};
use crate::common::{CodeDiagnostic, CodeError, FileId, HashSet, IndexMap, Marker};
use crate::diagnostics::DiagnosticContext;
use crate::parser::ParseCtx;
use crate::src::path::{Path, PathSegment};

use alumina_boot_macros::AstSerializable;
use indexmap::map::Entry;
use once_cell::unsync::OnceCell;

use std::cell::{Ref, RefCell};
use std::fmt::{Debug, Display, Formatter};
use std::rc::{Rc, Weak};

use tree_sitter::Node;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, AstSerializable)]
pub enum BoundItemType {
    ByValue,
    ByReference,
}

#[derive(Debug, Clone, AstSerializable)]
pub enum NamedItemKind<'ast> {
    Alias(Path<'ast>),
    Function(ItemP<'ast>),
    Method(ItemP<'ast>),
    TypeDef(ItemP<'ast>),
    Static(ItemP<'ast>),
    Const(ItemP<'ast>),
    Macro(ItemP<'ast>),
    Type(ItemP<'ast>),
    Mixin,
    Module,
    Protocol(ItemP<'ast>),
    Impl,
    EnumMember(ItemP<'ast>, Id),
    Placeholder(Id),
    Field,
    Local(Id),
    ConstLocal(Id),
    BoundValue(Id, Id, BoundItemType),
    Parameter(Id),
    MacroParameter(Id, bool),
    Closure(ItemP<'ast>),
    Anonymous,
}

impl Display for NamedItemKind<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            NamedItemKind::Alias(..) => write!(f, "alias"),
            NamedItemKind::Function(..) => write!(f, "function"),
            NamedItemKind::Method(..) => write!(f, "method"),
            NamedItemKind::Static(..) => write!(f, "static"),
            NamedItemKind::Const(..) => write!(f, "const"),
            NamedItemKind::ConstLocal(..) => write!(f, "const local"),
            NamedItemKind::Macro(..) => write!(f, "macro"),
            NamedItemKind::Type(..) => write!(f, "type"),
            NamedItemKind::Mixin => write!(f, "mixin"),
            NamedItemKind::Module => write!(f, "module"),
            NamedItemKind::Protocol(..) => write!(f, "protocol"),
            NamedItemKind::TypeDef(..) => write!(f, "typedef"),
            NamedItemKind::Impl => write!(f, "impl"),
            NamedItemKind::Placeholder(..) => write!(f, "placeholder"),
            NamedItemKind::Field => write!(f, "field"),
            NamedItemKind::EnumMember(..) => write!(f, "enum member"),
            NamedItemKind::Local(..) => write!(f, "local"),
            NamedItemKind::BoundValue(..) => write!(f, "bound value"),
            NamedItemKind::Parameter(..) => write!(f, "parameter"),
            NamedItemKind::MacroParameter(..) => write!(f, "macro parameter"),
            NamedItemKind::Closure(..) => write!(f, "closure"),
            NamedItemKind::Anonymous => write!(f, "anonymous"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct NamedItem<'ast, 'src> {
    pub kind: NamedItemKind<'ast>,
    pub node: Option<Node<'src>>,
    pub scope: Option<Scope<'ast, 'src>>,
    pub attributes: &'ast [Attribute<'ast>],
}

impl<'ast, 'src> NamedItem<'ast, 'src> {
    pub fn new(
        kind: NamedItemKind<'ast>,
        attributes: &'ast [Attribute],
        node: Node<'src>,
        child_scope: Option<Scope<'ast, 'src>>,
    ) -> Self {
        Self {
            kind,
            attributes,
            node: Some(node),
            scope: child_scope,
        }
    }

    pub fn new_default(
        kind: NamedItemKind<'ast>,
        node: Node<'src>,
        scope: Option<Scope<'ast, 'src>>,
    ) -> Self {
        Self {
            kind,
            attributes: &[],
            node: Some(node),
            scope,
        }
    }

    pub fn new_no_node(kind: NamedItemKind<'ast>, scope: Option<Scope<'ast, 'src>>) -> Self {
        Self {
            kind,
            attributes: &[],
            node: None,
            scope,
        }
    }

    pub fn ast_id(&self) -> Option<Id> {
        match &self.kind {
            NamedItemKind::Alias(_) => None,
            NamedItemKind::Function(item) => Some(item.id),
            NamedItemKind::Method(item) => Some(item.id),
            NamedItemKind::Static(item) => Some(item.id),
            NamedItemKind::Const(item) => Some(item.id),
            NamedItemKind::Macro(item) => Some(item.id),
            NamedItemKind::Type(item) => Some(item.id),
            NamedItemKind::Mixin => None,
            NamedItemKind::Module => None,
            NamedItemKind::Protocol(item) => Some(item.id),
            NamedItemKind::TypeDef(item) => Some(item.id),
            NamedItemKind::Impl => None,
            NamedItemKind::EnumMember(_, id) => Some(*id),
            NamedItemKind::Placeholder(id) => Some(*id),
            NamedItemKind::Field => None,
            NamedItemKind::Local(id) => Some(*id),
            NamedItemKind::BoundValue(_, id, _) => Some(*id),
            NamedItemKind::Parameter(id) => Some(*id),
            NamedItemKind::MacroParameter(id, _) => Some(*id),
            NamedItemKind::Anonymous => None,
            NamedItemKind::Closure(item) => Some(item.id),
            NamedItemKind::ConstLocal(id) => Some(*id),
        }
    }

    pub fn item(&self) -> Option<ItemP<'ast>> {
        match &self.kind {
            NamedItemKind::Alias(_) => None,
            NamedItemKind::Function(item) => Some(*item),
            NamedItemKind::Method(item) => Some(*item),
            NamedItemKind::Static(item) => Some(*item),
            NamedItemKind::Const(item) => Some(*item),
            NamedItemKind::Macro(item) => Some(*item),
            NamedItemKind::Type(item) => Some(*item),
            NamedItemKind::Mixin => None,
            NamedItemKind::Module => None,
            NamedItemKind::Protocol(item) => Some(*item),
            NamedItemKind::TypeDef(item) => Some(*item),
            NamedItemKind::Impl => None,
            NamedItemKind::EnumMember(item, _) => Some(*item),
            NamedItemKind::Placeholder(_) => None,
            NamedItemKind::Field => None,
            NamedItemKind::Local(_) => None,
            NamedItemKind::BoundValue(_, _, _) => None,
            NamedItemKind::Parameter(_) => None,
            NamedItemKind::MacroParameter(_, _) => None,
            NamedItemKind::Anonymous => None,
            NamedItemKind::Closure(item) => Some(*item),
            NamedItemKind::ConstLocal(_) => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, AstSerializable)]
pub enum ScopeType {
    Root,
    Module,
    Protocol,
    StructLike,
    Function,
    Macro,
    Closure,
    Impl,
    Enum,
    Block,
}

pub struct ScopeInner<'ast, 'src> {
    pub r#type: ScopeType,
    pub path: Path<'ast>,

    // We use IndexMap to preserve the order of items in the scope. While not important for
    // name resolution, it is important for e.g. struct layout, function signature, generic
    // parameter ordering, etc.
    pub items: IndexMap<Option<&'ast str>, Vec<NamedItem<'ast, 'src>>>,
    pub shadowed_items: Vec<Vec<NamedItem<'ast, 'src>>>,
    pub star_imports: Vec<Path<'ast>>,
    pub parent: Option<Weak<RefCell<ScopeInner<'ast, 'src>>>>,

    // This is additional information only used during construction and is not serialized.
    used_items: RefCell<HashSet<&'ast str>>,
    code: OnceCell<&'src ParseCtx<'src>>,
}

impl<'ast, 'src> ScopeInner<'ast, 'src> {
    pub fn all_items<'i>(
        &'i self,
    ) -> impl Iterator<Item = (Option<&'ast str>, &'i NamedItem<'ast, 'src>)> {
        self.items
            .iter()
            .flat_map(|(n, its)| its.iter().map(|i| (*n, i)))
            .chain(
                self.shadowed_items
                    .iter()
                    .flat_map(|its| its.iter().map(|i| (None, i))),
            )
    }

    pub fn grouped_items<'i>(
        &'i self,
    ) -> impl Iterator<Item = (Option<&'ast str>, &'i [NamedItem<'ast, 'src>])> {
        self.items
            .iter()
            .map(|(n, its)| (*n, its.as_slice()))
            .chain(self.shadowed_items.iter().map(|its| (None, its.as_slice())))
    }

    pub fn items_with_name<'i>(
        &'i self,
        name: &'ast str,
    ) -> impl Iterator<Item = &'i NamedItem<'ast, 'src>> {
        self.items
            .get(&Some(name))
            .into_iter()
            .flat_map(|its| its.iter())
    }

    pub fn unused_items<'i>(
        &'i self,
    ) -> impl Iterator<Item = (&'ast str, &'i NamedItem<'ast, 'src>)> {
        let used_items = self.used_items.borrow();
        self.items
            .iter()
            .filter_map(move |(n, its)| match n {
                Some(n) if used_items.contains(n) => None,
                Some(n) => Some(its.iter().map(|v| (*n, v))),
                None => None,
            })
            .flatten()
    }

    pub fn star_imports<'i>(&'i self) -> impl Iterator<Item = &'i Path<'ast>> {
        self.star_imports.iter()
    }
}

impl<'ast, 'src> Debug for ScopeInner<'ast, 'src> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), std::fmt::Error> {
        let mut builder = fmt.debug_struct(&format!("{:?}Scope({:?})", self.r#type, self.path));
        for (name, items) in &self.items {
            for item in items {
                builder.field(name.unwrap_or("<unnamed>"), item);
            }
        }
        builder.finish()
    }
}

#[derive(Clone)]
pub struct Scope<'ast, 'src>(pub Rc<RefCell<ScopeInner<'ast, 'src>>>);

impl<'ast, 'src> std::hash::Hash for Scope<'ast, 'src> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

impl<'ast, 'src> PartialEq for Scope<'ast, 'src> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<'ast, 'src> Eq for Scope<'ast, 'src> {}

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
    pub fn file_id(&self) -> FileId {
        self.code().unwrap().file_id()
    }

    pub fn new_root() -> Self {
        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type: ScopeType::Root,
            path: Path::root(),
            items: IndexMap::default(),
            shadowed_items: Vec::new(),
            star_imports: Vec::new(),
            parent: None,
            code: OnceCell::new(),
            used_items: RefCell::default(),
        })))
    }

    pub fn typ(&self) -> ScopeType {
        self.0.borrow().r#type
    }

    pub fn inner(&self) -> Ref<'_, ScopeInner<'ast, 'src>> {
        self.0.borrow()
    }

    pub fn code(&self) -> Option<&'src ParseCtx<'src>> {
        self.inner().code.get().copied()
    }

    pub fn path(&self) -> Path<'ast> {
        self.inner().path.clone()
    }

    pub fn named_child(&self, r#type: ScopeType, name: &'ast str) -> Self {
        let new_path = self.0.borrow().path.extend(PathSegment(name));
        let code = self.0.borrow().code.clone();

        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: new_path,
            items: IndexMap::default(),
            star_imports: Vec::new(),
            shadowed_items: Vec::new(),
            code,
            parent: Some(Rc::downgrade(&self.0)),
            used_items: RefCell::default(),
        })))
    }

    pub fn named_child_without_code(&self, r#type: ScopeType, name: &'ast str) -> Self {
        let new_path = self.0.borrow().path.extend(PathSegment(name));

        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: new_path,
            items: IndexMap::default(),
            star_imports: Vec::new(),
            shadowed_items: Vec::new(),
            code: OnceCell::new(),
            parent: Some(Rc::downgrade(&self.0)),
            used_items: RefCell::default(),
        })))
    }

    pub fn anonymous_child(&self, r#type: ScopeType) -> Self {
        let code = self.0.borrow().code.clone();

        Scope(Rc::new(RefCell::new(ScopeInner {
            r#type,
            path: self.path(),
            items: IndexMap::default(),
            star_imports: Vec::new(),
            shadowed_items: Vec::new(),
            code,
            parent: Some(Rc::downgrade(&self.0)),
            used_items: RefCell::default(),
        })))
    }

    pub fn set_code(&self, code: &'src ParseCtx<'src>) {
        if self.0.borrow().code.set(code).is_err() {
            panic!(
                "source code context is already set for {}",
                self.0.borrow().path
            );
        }
    }

    pub fn add_item(
        &self,
        name: Option<&'ast str>,
        item: NamedItem<'ast, 'src>,
    ) -> Result<(), CodeDiagnostic> {
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
                // Unnamed items do not generate name conflicts
                if name.is_none() {
                    existing.push(item);
                    return Ok(());
                } else {
                    let (type_count, impl_count) =
                        existing
                            .iter()
                            .fold((0, 0), |(type_count, impl_count), item| match item.kind {
                                NamedItemKind::Type(_) => (type_count + 1, impl_count),
                                NamedItemKind::Impl => (type_count, impl_count + 1),
                                _ => (type_count, impl_count),
                            });

                    if ((type_count == 1 || impl_count > 0)
                        && matches!(item.kind, NamedItemKind::Impl))
                        || (type_count == 0
                            && impl_count > 0
                            && matches!(item.kind, NamedItemKind::Type(_)))
                    {
                        existing.push(item);
                        existing.sort_by_key(|i| match i.kind {
                            NamedItemKind::Type(_) => 0,
                            NamedItemKind::Impl => 1,
                            _ => unreachable!(),
                        });
                        return Ok(());
                    }
                }

                if let ScopeType::Block = scope_type {
                    // In linear scopes we allow shadowing. We retain the shadowed item, as it may have been used already,
                    // but we rebind the name to the new item.
                    let old_item_group = std::mem::replace(existing, vec![item]);
                    current_scope.shadowed_items.push(old_item_group);
                    return Ok(());
                }
            }
        }

        Err(CodeDiagnostic::DuplicateName(name.unwrap().into()))
    }

    pub fn add_star_import(&self, path: Path<'ast>) {
        self.0.borrow_mut().star_imports.push(path.clone());
    }

    pub fn find_root(&self) -> Self {
        let mut current = self.clone();
        while let Some(parent) = current.parent() {
            current = parent;
        }
        current
    }

    pub fn find_super(&self) -> Option<Self> {
        // Function, struct, enum, ... are transparently scoped to their parent
        match self.0.borrow().r#type {
            ScopeType::Root => None,
            ScopeType::Module => self.parent(),
            _ => self.parent().and_then(|p| p.find_super()),
        }
    }

    pub fn find_containing_function(&self) -> Option<Self> {
        match self.0.borrow().r#type {
            ScopeType::Closure | ScopeType::Function => Some(self.clone()),
            _ => self.parent().and_then(|p| p.find_containing_function()),
        }
    }

    pub fn parent(&self) -> Option<Self> {
        self.inner()
            .parent
            .as_ref()
            .map(|parent| Self(parent.upgrade().unwrap()))
    }

    pub fn ensure_module(
        &self,
        path: Path<'ast>,
        kind: ScopeType,
    ) -> Result<Scope<'ast, 'src>, CodeDiagnostic> {
        if path.absolute {
            return self.find_root().ensure_module(
                Path {
                    absolute: false,
                    segments: path.segments.clone(),
                },
                kind,
            );
        }

        if path.segments.is_empty() {
            if self.typ() != kind {
                panic!(
                    "Scope type mismatch: expected {:?}, got {:?}",
                    kind,
                    self.typ()
                );
            }
            return Ok(self.clone());
        }

        let remainder = Path {
            absolute: false,
            segments: path.segments[1..].to_vec(),
        };

        for item in self.inner().items_with_name(path.segments[0].0) {
            if let NamedItemKind::Module = &item.kind {
                let child_scope = item.scope.as_ref().unwrap();
                return child_scope.ensure_module(remainder, kind);
            }
        }

        let child_scope = self.named_child_without_code(
            if path.segments.len() == 1 {
                kind
            } else {
                ScopeType::Module
            },
            path.segments[0].0,
        );
        self.add_item(
            Some(path.segments[0].0),
            NamedItem::new_no_node(NamedItemKind::Module, Some(child_scope.clone())),
        )?;

        child_scope.ensure_module(remainder, kind)
    }

    pub fn mark_used(&self, name: &'ast str) {
        self.0.borrow().used_items.borrow_mut().insert(name);
    }

    pub fn collect_items(&self, target: &mut HashSet<ItemP<'ast>>) {
        let inner = self.0.borrow();

        for (_, named_item) in inner.all_items() {
            if let Some(item) = named_item.item() {
                target.insert(item);
            }
            if let Some(scope) = &named_item.scope {
                scope.collect_items(target);
            }
        }
    }

    pub fn check_unused_items(&self, diag: &DiagnosticContext) {
        for (name, item) in self.inner().unused_items() {
            if name.starts_with('_') || name.starts_with("$_") {
                continue;
            }

            let Some(node) = item.node else {
                continue;
            };

            let kind = match item.kind {
                NamedItemKind::Local(_) | NamedItemKind::ConstLocal(_) => {
                    CodeDiagnostic::UnusedVariable(name.to_string())
                }
                NamedItemKind::BoundValue(_, _, _) => {
                    CodeDiagnostic::UnusedClosureBinding(name.to_string())
                }
                NamedItemKind::Alias(_) => CodeDiagnostic::UnusedImport(name.to_string()),
                NamedItemKind::MacroParameter(_, _) => {
                    CodeDiagnostic::UnusedParameter(name.to_string())
                }
                NamedItemKind::Parameter(_) => {
                    if name == "self" {
                        continue;
                    }

                    CodeDiagnostic::UnusedParameter(name.to_string())
                }
                _ => continue,
            };

            let span = Span::from_node(self.file_id(), node);

            diag.add_warning(CodeError {
                kind,
                backtrace: vec![Marker::Span(span)],
            })
        }
    }
}
