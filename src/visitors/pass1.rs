use crate::common::{AluminaError, SyntaxError, ToSyntaxError};
use crate::context::GlobalCtx;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::AluminaVisitor;

use std::result::Result;
use tree_sitter::Node;

use super::{ScopedPathVisitor, VisitorExt};

pub struct UseClauseVisitor<'tcx> {
    source: &'tcx str,
    prefix: Path<'tcx>,
    current_scope: Scope<'tcx>,
}

impl<'tcx> UseClauseVisitor<'tcx> {
    fn new(source: &'tcx str, current_scope: Scope<'tcx>) -> Self {
        Self {
            source,
            prefix: Path::default(),
            current_scope,
        }
    }

    fn parse_use_path(&mut self, node: Node<'tcx>) -> Result<Path<'tcx>, SyntaxError<'tcx>> {
        let mut visitor = ScopedPathVisitor::new(self.source, self.current_scope.clone());
        visitor.visit(node)
    }
}

impl<'tcx> AluminaVisitor<'tcx> for UseClauseVisitor<'tcx> {
    type ReturnType = Result<(), SyntaxError<'tcx>>;

    fn visit_use_as_clause(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let alias = &self.source[node.child_by_field_name("alias").unwrap().byte_range()];
        self.current_scope
            .add_item(alias, Item::Alias(self.prefix.join_with(path)))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_use_list(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        self.visit_children_by_field(node, "item")
    }

    fn visit_scoped_use_list(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let suffix = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let new_prefix = self.prefix.join_with(suffix);
        let old_prefix = std::mem::replace(&mut self.prefix, new_prefix);

        self.visit(node.child_by_field_name("list").unwrap())?;
        self.prefix = old_prefix;

        Ok(())
    }

    fn visit_identifier(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let alias = &self.source[node.byte_range()];
        self.current_scope
            .add_item(alias, Item::Alias(self.prefix.extend(PathSegment(alias))))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_scoped_identifier(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];
        self.current_scope
            .add_item(
                name,
                Item::Alias(self.prefix.join_with(path.extend(PathSegment(name)))),
            )
            .to_syntax_error(node)?;

        Ok(())
    }
}

pub struct FirstPassVisitor<'tcx> {
    source: &'tcx str,
    context: &'tcx GlobalCtx<'tcx>,
    current_scope: Scope<'tcx>,
}

impl<'tcx> FirstPassVisitor<'tcx> {
    pub fn new(
        context: &'tcx GlobalCtx<'tcx>,
        source: &'tcx str,
        current_scope: Scope<'tcx>,
    ) -> Self {
        Self {
            context,
            source,
            current_scope,
        }
    }
}

macro_rules! with_child_scope {
    ($self:ident, $scope:expr, $body:block) => {
        let previous_scope = std::mem::replace(&mut $self.current_scope, $scope);
        $body
        $self.current_scope = previous_scope;
    };
}

impl<'tcx> FirstPassVisitor<'tcx> {
    fn parse_name(&self, node: Node<'tcx>) -> &'tcx str {
        let name_node = node.child_by_field_name("name").unwrap();
        &self.source[name_node.byte_range()]
    }
}

impl<'tcx> AluminaVisitor<'tcx> for FirstPassVisitor<'tcx> {
    type ReturnType = Result<(), SyntaxError<'tcx>>;

    fn visit_source_file(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        self.visit_children(node)
    }

    fn visit_mod_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Module, name);

        self.current_scope
            .add_item(name, Item::Module(child_scope.clone()))
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_struct_definition(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Struct, name);

        self.current_scope
            .add_item(
                name,
                Item::Type(self.context.make_symbol(), node, child_scope.clone()),
            )
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_impl_block(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        let child_scope = self.current_scope.make_child(ScopeType::Impl, name);

        self.current_scope
            .add_item(name, Item::Impl(child_scope.clone()))
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

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
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .to_syntax_error(node)?;

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
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "parameters")?;
        });

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
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "parameters")?;
        });

        Ok(())
    }

    fn visit_generic_argument_list(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let mut cursor = node.walk();
        for argument in node.children_by_field_name("argument", &mut cursor) {
            let name = &self.source[argument.byte_range()];
            self.current_scope
                .add_item(name, Item::Placeholder(self.context.make_symbol()))
                .to_syntax_error(node)?;
        }

        Ok(())
    }

    fn visit_parameter(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);

        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_parameter_list(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_enum_item(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let name = self.parse_name(node);
        self.current_scope
            .add_item(name, Item::Field(self.context.make_symbol(), node))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_use_declaration(&mut self, node: Node<'tcx>) -> Result<(), SyntaxError<'tcx>> {
        let mut visitor = UseClauseVisitor::new(self.source, self.current_scope.clone());
        visitor.visit(node.child_by_field_name("argument").unwrap())?;

        Ok(())
    }
}
