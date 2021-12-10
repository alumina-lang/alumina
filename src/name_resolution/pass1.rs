use crate::common::{ArenaAllocatable, SyntaxError, ToSyntaxError};

use crate::ast::{AstCtx, ItemP};
use crate::name_resolution::scope::{NamedItem, Scope, ScopeType};
use crate::parser::{AluminaVisitor, ParseCtx};

use std::result::Result;
use tree_sitter::Node;

use crate::visitors::{UseClauseVisitor, VisitorExt};

pub struct FirstPassVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    scope: Scope<'ast, 'src>,
    code: &'src ParseCtx<'src>,
    enum_item: Option<ItemP<'ast>>,
}

impl<'ast, 'src> FirstPassVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        Self {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            enum_item: None,
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

impl<'ast, 'src> FirstPassVisitor<'ast, 'src> {
    fn parse_name(&self, node: Node<'src>) -> &'ast str {
        let name_node = node.child_by_field_name("name").unwrap();
        self.code.node_text(name_node).alloc_on(self.ast)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for FirstPassVisitor<'ast, 'src> {
    type ReturnType = Result<(), SyntaxError<'src>>;

    fn visit_source_file(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        self.visit_children(node)
    }

    fn visit_mod_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Module, name);

        self.scope
            .add_item(name, NamedItem::Module(child_scope.clone()))
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
                NamedItem::Type(self.ast.make_symbol(), node, child_scope.clone()),
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
            .add_item(name, NamedItem::Impl(child_scope.clone()))
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Enum, name);
        let sym = self.ast.make_symbol();
        self.scope
            .add_item(name, NamedItem::Type(sym, node, child_scope.clone()))
            .to_syntax_error(node)?;

        with_child_scope!(self, child_scope, {
            self.enum_item = Some(sym);
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_item(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        self.scope
            .add_item(
                name,
                NamedItem::EnumMember(self.enum_item.unwrap(), self.ast.make_id(), node),
            )
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);
        self.scope
            .add_item(name, NamedItem::Field(node))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_function_definition(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Function, name);

        self.scope
            .add_item(
                name,
                NamedItem::Function(self.ast.make_symbol(), node, child_scope.clone()),
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
                NamedItem::Function(self.ast.make_symbol(), node, child_scope.clone()),
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
            let name = self.code.node_text(argument).alloc_on(self.ast);
            self.scope
                .add_item(name, NamedItem::Placeholder(self.ast.make_id()))
                .to_syntax_error(node)?;
        }

        Ok(())
    }

    fn visit_parameter(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name = self.parse_name(node);

        self.scope
            .add_item(name, NamedItem::Parameter(self.ast.make_id(), node))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_parameter_list(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_use_declaration(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let mut visitor = UseClauseVisitor::new(self.ast, self.scope.clone());
        visitor.visit(node.child_by_field_name("argument").unwrap())?;

        Ok(())
    }
}
