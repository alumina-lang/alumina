use crate::parser::AluminaVisitor;
use crate::{common::*, GlobalCtx, SymbolP};

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::result::Result;
use tree_sitter::Node;

use std::cell::RefCell;
use std::rc::{Rc, Weak};

#[derive(Debug)]
pub enum Item<'tcx> {
    Function(SymbolP<'tcx>, Node<'tcx>),
    Type(SymbolP<'tcx>, Node<'tcx>, Scope<'tcx>),
    Module(Scope<'tcx>),
    Impl(Scope<'tcx>),
    Field(SymbolP<'tcx>, Node<'tcx>),
    Alias(Path<'tcx>),
}

#[derive(Debug)]
pub enum ScopeType {
    Module,
    Struct,
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
            r#type: ScopeType::Module,
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
                if existing.len() == 1 {
                    if (matches!(existing[0], Item::Type(_, _, _)) && matches!(item, Item::Impl(_)))
                        || (matches!(existing[0], Item::Impl(_))
                            && matches!(item, Item::Type(_, _, _)))
                    {
                        existing.push(item);
                        return Ok(());
                    }
                }
            }
        }

        Err(GenericError("duplicate item"))
    }

    fn root(&self) -> Self {
        let mut current = self.clone();
        while let Some(parent) = self.parent() {
            current = parent;
        }
        current
    }

    fn parent(&self) -> Option<Self> {
        self.0
            .borrow()
            .parent
            .as_ref()
            .map(|parent| Self(parent.upgrade().unwrap()))
    }

    fn resolve_scope(&self, path: &Path<'tcx>) -> Result<Scope<'tcx>, GenericError> {
        let mut current_scope = self.0.borrow_mut();
        let mut current_path = current_scope.path.clone();

        if path.absolute {
            return self.root().resolve_scope(&Path {
                absolute: false,
                segments: path.segments.clone(),
            });
        }

        Ok(self.clone())
    }
}

pub struct FirstPassVisitor<'tcx> {
    source: &'tcx str,
    context: &'tcx GlobalCtx<'tcx>,
    root_scope: Scope<'tcx>,
    current_scope: Scope<'tcx>,
}

impl<'tcx> FirstPassVisitor<'tcx> {
    pub fn new(context: &'tcx GlobalCtx<'tcx>, source: &'tcx str, root_scope: Scope<'tcx>) -> Self {
        Self {
            context,
            source,
            root_scope: root_scope.clone(),
            current_scope: root_scope,
        }
    }
}

impl<'tcx> FirstPassVisitor<'tcx> {
    fn visit_children(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let mut cursor = node.walk();
        for node in node.children(&mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn visit_children_by_field(
        &mut self,
        node: Node<'tcx>,
        field: &'static str,
    ) -> Result<(), SyntaxError<'tcx>> {
        let mut cursor = node.walk();
        for node in node.children_by_field_name(field, &mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn parse_name(&self, node: Node<'tcx>) -> &'tcx str {
        let name_node = node.child_by_field_name("name").unwrap();
        &self.source[name_node.byte_range()]
    }

    fn parse_use_path(&mut self, node: Node<'tcx>) -> Result<Path<'tcx>, SyntaxError<'tcx>> {
        let path = match node.kind() {
            "super" => {
                let current_path = self.current_scope.0.borrow().path.clone();
                println!("{}", current_path);
                if current_path.segments.len() == 1 {
                    return Err(SyntaxError("super not allowed in root scope", node));
                }
                current_path.pop()
            }
            "crate" => self.root_scope.0.borrow().path.clone(),
            "identifier" => {
                let name = &self.source[node.byte_range()];
                PathSegment(name).into()
            }
            "scoped_identifier" => {
                let subpath = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
                let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];
                subpath.extend(PathSegment(name))
            }
            _ => return Err(SyntaxError("no.", node)),
        };

        Ok(path)
    }

    fn parse_use_clause(
        &mut self,
        node: Node<'tcx>,
        prefix: &Path<'tcx>,
    ) -> Result<(), SyntaxError<'tcx>> {
        match node.kind() {
            "use_as_clause" => {
                let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
                let alias = &self.source[node.child_by_field_name("alias").unwrap().byte_range()];
                self.current_scope
                    .add_item(alias, Item::Alias(prefix.join_with(path)))
                    .map_err(|w| SyntaxError(w.0, node))?;
            }
            "use_list" => {
                let mut cursor = node.walk();
                for node in node.children_by_field_name("item", &mut cursor) {
                    self.parse_use_clause(node, prefix)?;
                }
            }
            "scoped_use_list" => {
                let path = prefix
                    .join_with(self.parse_use_path(node.child_by_field_name("path").unwrap())?);
                self.parse_use_clause(node.child_by_field_name("list").unwrap(), &path)?;
            }
            "identifier" => {
                let alias = &self.source[node.byte_range()];
                self.current_scope
                    .add_item(alias, Item::Alias(prefix.extend(PathSegment(alias))))
                    .map_err(|w| SyntaxError(w.0, node))?;
            }
            "scoped_identifier" => {
                let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
                let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];
                self.current_scope
                    .add_item(
                        name,
                        Item::Alias(prefix.join_with(path.extend(PathSegment(name)))),
                    )
                    .map_err(|w| SyntaxError(w.0, node))?;
            }
            _ => return Err(SyntaxError("no.", node)),
        }

        Ok(())
    }

    fn pop_scope(&mut self) {
        self.current_scope = self.current_scope.parent().unwrap()
    }
}

impl<'tcx> AluminaVisitor<'tcx> for FirstPassVisitor<'tcx> {
    type ReturnType = Result<(), SyntaxError<'tcx>>;

    fn visit_source_file(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        self.visit_children(node)
    }

    fn visit_struct_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Struct, name);

        self.current_scope
            .add_item(
                name,
                Item::Type(self.context.make_symbol(), node, child_scope.clone()),
            )
            .map_err(|w| SyntaxError(w.0, node))?;

        self.current_scope = child_scope;
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_impl_block(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Impl, name);

        self.current_scope
            .add_item(name, Item::Impl(child_scope.clone()))
            .map_err(|w| SyntaxError(w.0, node))?;

        self.current_scope = child_scope;
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_enum_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Enum, name);
        self.current_scope
            .add_item(
                name,
                Item::Type(self.context.make_symbol(), node, child_scope.clone()),
            )
            .map_err(|w| SyntaxError(w.0, node))?;

        self.current_scope = child_scope;
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_mod_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Module, name);

        self.current_scope
            .add_item(name, Item::Module(child_scope.clone()))
            .map_err(|w| SyntaxError(w.0, node))?;

        self.current_scope = child_scope;
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_function_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Function(self.context.make_symbol(), node))
            .map_err(|w| SyntaxError(w.0, node))?;

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .map_err(|w| SyntaxError(w.0, node))?;

        Ok(())
    }

    fn visit_extern_function_declaration(
        &mut self,
        node: Node<'tcx>,
    ) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Function(self.context.make_symbol(), node))
            .map_err(|w| SyntaxError(w.0, node))?;

        Ok(())
    }

    fn visit_enum_item(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .map_err(|w| SyntaxError(w.0, node))?;

        Ok(())
    }

    fn visit_use_declaration(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let prefix = Path::default();
        self.parse_use_clause(node.child_by_field_name("argument").unwrap(), &prefix)
    }
}
