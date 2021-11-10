use crate::common::*;

use std::collections::HashMap;
use std::fmt::Debug;
use std::result::Result;
use tree_sitter::Node;

#[derive(Debug)]
pub enum SymbolItem<'syntax> {
    Function(Node<'syntax>),
    Type(Node<'syntax>),
    Field(Node<'syntax>),
    Alias(Path<'syntax>),
}

#[derive(Debug)]
pub enum ScopeType {
    Module,
    Struct,
    Enum,
}

#[derive(Debug)]
pub struct Scope<'syntax> {
    r#type: ScopeType,
    path: Path<'syntax>,
    symbols: HashMap<&'syntax str, SymbolItem<'syntax>>,
    children: Vec<Rc<RefCell<Scope<'syntax>>>>,
    parent: Option<Weak<RefCell<Scope<'syntax>>>>,
}

use std::cell::RefCell;
use std::rc::{Rc, Weak};

#[derive(Debug)]
pub struct FirstPassVisitor<'syntax> {
    source: &'syntax str,
    pub root_scope: Rc<RefCell<Scope<'syntax>>>,
    current_scope: Rc<RefCell<Scope<'syntax>>>,
    current_path: Path<'syntax>,
}

impl<'syntax> FirstPassVisitor<'syntax> {
    pub fn new(source: &'syntax str, root_module: Path<'syntax>) -> Self {
        let scope = Rc::new(RefCell::new(Scope {
            r#type: ScopeType::Module,
            path: root_module.clone(),
            symbols: HashMap::new(),
            children: Vec::new(),
            parent: None,
        }));

        Self {
            source,
            current_path: root_module,
            root_scope: scope.clone(),
            current_scope: scope,
        }
    }
}

impl<'syntax> FirstPassVisitor<'syntax> {
    fn visit_children(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let mut cursor = node.walk();
        for node in node.children(&mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn visit_children_by_field(
        &mut self,
        node: Node<'syntax>,
        field: &'static str,
    ) -> Result<(), SyntaxError<'syntax>> {
        let mut cursor = node.walk();
        for node in node.children_by_field_name(field, &mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn parse_name(&self, node: Node<'syntax>) -> &'syntax str {
        let name_node = node.child_by_field_name("name").unwrap();
        &self.source[name_node.byte_range()]
    }

    fn add_symbol(
        &self,
        name: &'syntax str,
        item: SymbolItem<'syntax>,
    ) -> Option<SymbolItem<'syntax>> {
        self.current_scope.borrow_mut().symbols.insert(name, item)
    }

    fn push_scope(&mut self, name: &'syntax str, type_: ScopeType) {
        let scope = Rc::new(RefCell::new(Scope {
            r#type: type_,
            path: self.current_path.extend(PathSegment::Ident(name)),
            symbols: HashMap::new(),
            children: Vec::new(),
            parent: Some(Rc::downgrade(&self.current_scope)),
        }));

        self.current_scope.borrow_mut().children.push(scope.clone());
        self.current_scope = scope;
    }

    fn parse_use_path(
        &mut self,
        node: Node<'syntax>,
    ) -> Result<Path<'syntax>, SyntaxError<'syntax>> {
        let path = match node.kind() {
            "super" => {
                let current_path = self.current_scope.borrow().path.clone();
                println!("{}", current_path);
                if current_path.segments.len() == 1 {
                    return Err(SyntaxError("super not allowed in root scope", node));
                }
                current_path.pop()
            }
            "crate" => self.root_scope.borrow().path.clone(),
            "identifier" => {
                let name = &self.source[node.byte_range()];
                PathSegment::Ident(name).into()
            }
            "scoped_identifier" => {
                let subpath = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
                let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];
                subpath.extend(PathSegment::Ident(name))
            }
            _ => return Err(SyntaxError("no.", node)),
        };

        Ok(path)
    }

    fn parse_use_clause(
        &mut self,
        node: Node<'syntax>,
        prefix: &Path<'syntax>,
    ) -> Result<(), SyntaxError<'syntax>> {
        match node.kind() {
            "use_as_clause" => {
                let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
                let alias = &self.source[node.child_by_field_name("alias").unwrap().byte_range()];
                self.add_symbol(alias, SymbolItem::Alias(prefix.join_with(path)));
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
                self.add_symbol(
                    alias,
                    SymbolItem::Alias(prefix.extend(PathSegment::Ident(alias))),
                );
            }
            "scoped_identifier" => {
                let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
                let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];
                self.add_symbol(
                    name,
                    SymbolItem::Alias(prefix.join_with(path.extend(PathSegment::Ident(name)))),
                );
            }
            _ => return Err(SyntaxError("no.", node)),
        }

        Ok(())
    }

    fn pop_scope(&mut self) {
        let parent = self
            .current_scope
            .borrow()
            .parent
            .as_ref()
            .unwrap()
            .upgrade();

        self.current_scope = parent.unwrap()
    }
}

impl<'syntax> AluminaVisitor<'syntax> for FirstPassVisitor<'syntax> {
    type ReturnType = Result<(), SyntaxError<'syntax>>;

    fn visit_source_file(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        self.visit_children(node)
    }

    fn visit_struct_definition(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let name = self.parse_name(node);

        if self.add_symbol(name, SymbolItem::Type(node)).is_some() {
            return Err(SyntaxError("duplicate symbol", node));
        }

        self.push_scope(name, ScopeType::Struct);
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_enum_definition(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let name = self.parse_name(node);

        if self.add_symbol(name, SymbolItem::Type(node)).is_some() {
            return Err(SyntaxError("duplicate symbol", node));
        }

        self.push_scope(name, ScopeType::Enum);
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_mod_definition(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let name = self.parse_name(node);

        self.push_scope(name, ScopeType::Module);
        self.visit_children_by_field(node, "body")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_function_definition(
        &mut self,
        node: Node<'syntax>,
    ) -> Result<(), SyntaxError<'syntax>> {
        let name = self.parse_name(node);
        if self.add_symbol(name, SymbolItem::Function(node)).is_some() {
            return Err(SyntaxError("duplicate symbol", node));
        }

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let name = self.parse_name(node);
        if self.add_symbol(name, SymbolItem::Field(node)).is_some() {
            return Err(SyntaxError("duplicate symbol", node));
        }

        Ok(())
    }

    fn visit_enum_item(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let name = self.parse_name(node);
        if self.add_symbol(name, SymbolItem::Field(node)).is_some() {
            return Err(SyntaxError("duplicate symbol", node));
        }

        Ok(())
    }

    fn visit_use_declaration(&mut self, node: Node<'syntax>) -> Result<(), SyntaxError<'syntax>> {
        let prefix = Path::default();
        self.parse_use_clause(node.child_by_field_name("argument").unwrap(), &prefix)
    }
}
