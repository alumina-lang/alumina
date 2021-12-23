use crate::common::{AluminaError, ArenaAllocatable, WithSpanDuringParsing};

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
    type ReturnType = Result<(), AluminaError>;

    fn visit_source_file(&mut self, node: Node<'src>) -> Self::ReturnType {
        self.visit_children(node)
    }

    fn visit_mod_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Module, name);

        self.scope
            .add_item(Some(name), NamedItem::Module(child_scope.clone()))
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_protocol_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Protocol, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::Protocol(self.ast.make_symbol(), node, child_scope.clone()),
            )
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_struct_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::StructLike, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::Type(self.ast.make_symbol(), node, child_scope.clone()),
            )
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_impl_block(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Impl, name);

        self.scope
            .add_item(Some(name), NamedItem::Impl(node, child_scope.clone()))
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Enum, name);
        let sym = self.ast.make_symbol();
        self.scope
            .add_item(Some(name), NamedItem::Type(sym, node, child_scope.clone()))
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.enum_item = Some(sym);
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        self.scope
            .add_item(
                Some(name),
                NamedItem::EnumMember(self.enum_item.unwrap(), self.ast.make_id(), node),
            )
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);
        self.scope
            .add_item(Some(name), NamedItem::Field(node))
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_function_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Function, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::Function(self.ast.make_symbol(), node, child_scope.clone()),
            )
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "parameters")?;
        });

        Ok(())
    }

    fn visit_mixin(&mut self, node: Node<'src>) -> Self::ReturnType {
        let child_scope = self.scope.anonymous_child(ScopeType::Function);

        self.scope
            .add_item(None, NamedItem::Mixin(node, child_scope.clone()))
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
        });

        Ok(())
    }

    fn visit_static_declaration(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);
        self.scope
            .add_item(Some(name), NamedItem::Static(self.ast.make_symbol(), node))
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_generic_argument_list(&mut self, node: Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        for argument in node.children_by_field_name("argument", &mut cursor) {
            let name = self
                .code
                .node_text(argument.child_by_field_name("placeholder").unwrap())
                .alloc_on(self.ast);
            self.scope
                .add_item(
                    Some(name),
                    NamedItem::Placeholder(self.ast.make_id(), argument),
                )
                .with_span(&self.scope, node)?;
        }

        Ok(())
    }

    fn visit_parameter(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        self.scope
            .add_item(Some(name), NamedItem::Parameter(self.ast.make_id(), node))
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_macro_parameter(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        self.scope
            .add_item(
                Some(name),
                NamedItem::MacroParameter(
                    self.ast.make_id(),
                    node.child_by_field_name("et_cetera").is_some(),
                ),
            )
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_parameter_list(&mut self, node: Node<'src>) -> Self::ReturnType {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_macro_parameter_list(&mut self, node: Node<'src>) -> Self::ReturnType {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_use_declaration(&mut self, node: Node<'src>) -> Self::ReturnType {
        let mut visitor = UseClauseVisitor::new(self.ast, self.scope.clone());
        visitor.visit(node.child_by_field_name("argument").unwrap())?;

        Ok(())
    }

    fn visit_macro_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Macro, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::Macro(self.ast.make_symbol(), node, child_scope.clone()),
            )
            .with_span(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "parameters")?;
        });

        Ok(())
    }

    fn visit_const_declaration(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        self.scope
            .add_item(Some(name), NamedItem::Const(self.ast.make_symbol(), node))
            .with_span(&self.scope, node)?;

        Ok(())
    }
}
