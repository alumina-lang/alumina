use crate::common::{SyntaxError, ToSyntaxError};

use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::{AluminaVisitor, ParseCtx};

use std::result::Result;
use tree_sitter::Node;

use super::{ScopedPathVisitor, UseClauseVisitor, VisitorExt};
pub struct FirstPassVisitor<'gcx, 'src> {
    scope: Scope<'gcx, 'src>,
    parse_ctx: ParseCtx<'gcx, 'src>,
}

impl<'gcx, 'src> FirstPassVisitor<'gcx, 'src> {
    pub fn new(scope: Scope<'gcx, 'src>) -> Self {
        Self {
            parse_ctx: scope
                .parse_ctx()
                .expect("cannot run on scope without parse context"),
            scope,
        }
    }
}

macro_rules! with_child_scope {
    ($self:ident, $scope:expr, $body:block) => {
        let previous_scope = std::mem::replace(&mut $self.scope, $scope);
        $body
        $self.scope = previous_scope;
    };
}

impl<'gcx, 'src> FirstPassVisitor<'gcx, 'src> {
    fn parse_name(&self, node: Node<'src>) -> &'src str {
        let name_node = node.child_by_field_name("name").unwrap();
        self.parse_ctx.node_text(name_node)
    }
}

impl<'gcx, 'src> AluminaVisitor<'src> for FirstPassVisitor<'gcx, 'src> {
    type ReturnType = Result<(), SyntaxError<'src>>;

    fn visit_source_file(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        self.visit_children(node)
    }

    fn visit_mod_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Module, name);

        self.scope
            .add_item(name, Item::Module(child_scope.clone()))
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_struct_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Struct, name);

        self.scope
            .add_item(
                name,
                Item::Type(
                    self.parse_ctx.make_symbol(Some(name)),
                    node,
                    child_scope.clone(),
                ),
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

    fn visit_impl_block(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Impl, name);

        self.scope
            .add_item(name, Item::Impl(child_scope.clone()))
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Enum, name);
        self.scope
            .add_item(
                name,
                Item::Type(
                    self.parse_ctx.make_symbol(Some(name)),
                    node,
                    child_scope.clone(),
                ),
            )
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);
        self.scope
            .add_item(
                name,
                Item::Field(self.parse_ctx.make_symbol(Some(name)), node),
            )
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_function_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Function, name);

        self.scope
            .add_item(
                name,
                Item::Function(
                    self.parse_ctx.make_symbol(Some(name)),
                    node,
                    child_scope.clone(),
                ),
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
        node: Node<'src>,
    ) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Function, name);

        self.scope
            .add_item(
                name,
                Item::Function(
                    self.parse_ctx.make_symbol(Some(name)),
                    node,
                    child_scope.clone(),
                ),
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

    fn visit_generic_argument_list(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let mut cursor = node.walk();
        for argument in node.children_by_field_name("argument", &mut cursor) {
            let name = self.parse_ctx.node_text(argument);
            self.scope
                .add_item(
                    name,
                    Item::Placeholder(self.parse_ctx.make_symbol(Some(name))),
                )
                .to_syntax_error(node)?;
        }

        Ok(())
    }

    fn visit_parameter(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        self.scope
            .add_item(
                name,
                Item::Field(self.parse_ctx.make_symbol(Some(name)), node),
            )
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_parameter_list(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_enum_item(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);
        self.scope
            .add_item(
                name,
                Item::Field(self.parse_ctx.make_symbol(Some(name)), node),
            )
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_use_declaration(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let mut visitor = UseClauseVisitor::new(self.scope.clone());
        visitor.visit(node.child_by_field_name("argument").unwrap())?;

        Ok(())
    }
}
