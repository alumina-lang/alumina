use crate::common::SyntaxError;
use crate::context::GlobalCtx;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::AluminaVisitor;

use std::result::Result;
use tree_sitter::Node;

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
            "super" => self
                .current_scope
                .find_super()
                .ok_or(SyntaxError("super not allowed", node))?
                .path(),

            "crate" => self
                .current_scope
                .find_crate()
                .ok_or(SyntaxError("crate not allowed", node))?
                .path(),

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
        if let Some(f) = node.child_by_field_name("type_arguments") {
            self.visit(f)?;
        }
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

    fn visit_struct_field(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .map_err(|w| SyntaxError(w.0, node))?;

        Ok(())
    }

    fn visit_function_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        let child_scope = self.current_scope.make_child(ScopeType::Function, name);

        self.current_scope
            .add_item(
                name,
                Item::Function(self.context.make_symbol(), node, child_scope.clone()),
            )
            .map_err(|w| SyntaxError(w.0, node))?;

        self.current_scope = child_scope;
        if let Some(f) = node.child_by_field_name("type_arguments") {
            self.visit(f)?;
        }
        self.visit_children_by_field(node, "parameters")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_extern_function_declaration(
        &mut self,
        node: Node<'tcx>,
    ) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        let child_scope = self.current_scope.make_child(ScopeType::Function, name);

        self.current_scope
            .add_item(
                name,
                Item::Function(self.context.make_symbol(), node, child_scope.clone()),
            )
            .map_err(|w| SyntaxError(w.0, node))?;

        self.current_scope = child_scope;
        if let Some(f) = node.child_by_field_name("type_arguments") {
            self.visit(f)?;
        }
        self.visit_children_by_field(node, "parameters")?;
        self.pop_scope();

        Ok(())
    }

    fn visit_generic_argument_list(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let mut cursor = node.walk();
        for argument in node.children_by_field_name("argument", &mut cursor) {
            let name = &self.source[argument.byte_range()];
            self.current_scope
                .add_item(name, Item::Placeholder(self.context.make_symbol()))
                .map_err(|w| SyntaxError(w.0, node))?;
        }

        Ok(())
    }

    fn visit_parameter(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .map_err(|w| SyntaxError(w.0, node))?;

        Ok(())
    }

    fn visit_parameter_list(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        self.visit_children_by_field(node, "parameter")
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
