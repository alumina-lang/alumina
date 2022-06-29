use crate::common::{AluminaError, ArenaAllocatable, CodeErrorKind, WithSpanDuringParsing};

use crate::ast::{AstCtx, Attribute, ItemP};
use crate::global_ctx::GlobalCtx;
use crate::name_resolution::scope::{NamedItemKind, Scope, ScopeType};
use crate::parser::{AluminaVisitor, ParseCtx};

use std::result::Result;
use tree_sitter::Node;

use crate::visitors::{AttributeVisitor, UseClauseVisitor, VisitorExt};

use super::path::Path;
use super::scope::NamedItem;

pub struct FirstPassVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    scope: Scope<'ast, 'src>,
    code: &'src ParseCtx<'src>,
    enum_item: Option<ItemP<'ast>>,

    in_a_container: bool,
    main_module_path: Option<Path<'ast>>,
    main_candidate: Option<ItemP<'ast>>,
}

impl<'ast, 'src> FirstPassVisitor<'ast, 'src> {
    pub fn new(global_ctx: GlobalCtx, ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        Self {
            global_ctx,
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            in_a_container: false,
            enum_item: None,
            main_module_path: None,
            main_candidate: None,
        }
    }

    pub fn with_main(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
    ) -> Self {
        Self {
            global_ctx,
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            main_module_path: Some(scope.path()),
            scope,
            in_a_container: false,
            enum_item: None,
            main_candidate: None,
        }
    }

    pub fn main_candidate(&self) -> Option<ItemP<'ast>> {
        self.main_candidate
    }
}

macro_rules! with_child_scope {
    ($self:ident, $scope:expr, $body:block) => {
        let previous_scope = std::mem::replace(&mut $self.scope, $scope);
        $body
        $self.scope = previous_scope;
    };
}

macro_rules! with_child_scope_container {
    ($self:ident, $scope:expr, $body:block) => {
        let previous_scope = std::mem::replace(&mut $self.scope, $scope);
        let previous_in_a_container = $self.in_a_container;
        $body
        $self.scope = previous_scope;
        $self.in_a_container = previous_in_a_container;
    };
}

impl<'ast, 'src> FirstPassVisitor<'ast, 'src> {
    fn parse_name(&self, node: Node<'src>) -> &'ast str {
        let name_node = node.child_by_field_name("name").unwrap();
        self.code.node_text(name_node).alloc_on(self.ast)
    }
}

macro_rules! parse_attributes {
    (@, $self:expr, $node:expr, $item:expr) => {
        match AttributeVisitor::parse_attributes($self.global_ctx.clone(), $self.ast, $self.scope.clone(), $node, $item)? {
            Some(attributes) => attributes,
            None => return Ok(()),
        }
    };
    ($self:expr, $node:expr, $item:expr) => {
        parse_attributes!(@, $self, $node, Some($item))
    };
    ($self:expr, $node:expr) => {
        parse_attributes!(@, $self, $node, None)
    };
}

pub(crate) use parse_attributes;

impl<'ast, 'src> AluminaVisitor<'src> for FirstPassVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_source_file(&mut self, node: Node<'src>) -> Self::ReturnType {
        parse_attributes!(self, node);
        self.visit_children_by_field(node, "body")
    }

    fn visit_mod_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let attributes = parse_attributes!(self, node);
        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Module, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(NamedItemKind::Module(child_scope.clone()), attributes),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_top_level_block(&mut self, node: Node<'src>) -> Self::ReturnType {
        let _ = parse_attributes!(self, node);

        self.visit_children_by_field(node, "items")
    }

    fn visit_protocol_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Protocol, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::Protocol(item, node, child_scope.clone()),
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope_container!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_struct_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::StructLike, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::Type(item, node, child_scope.clone()),
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_impl_block(&mut self, node: Node<'src>) -> Self::ReturnType {
        let attributes = parse_attributes!(self, node);

        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Impl, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(NamedItemKind::Impl(node, child_scope.clone()), attributes),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope_container!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Enum, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::Type(item, node, child_scope.clone()),
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.enum_item = Some(item);
            self.visit_children_by_field(node, "body")?;
        });

        Ok(())
    }

    fn visit_enum_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        let attributes = parse_attributes!(self, node);

        let name = self.parse_name(node);
        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::EnumMember(self.enum_item.unwrap(), self.ast.make_id(), node),
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_struct_field(&mut self, node: Node<'src>) -> Self::ReturnType {
        let attributes = parse_attributes!(self, node);

        let name = self.parse_name(node);
        self.scope
            .add_item(
                Some(name),
                NamedItem::new(NamedItemKind::Field(node), attributes),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_function_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);

        if let Some(path) = self.main_module_path.as_ref() {
            if self.global_ctx.cfg("test").is_some() {
                if attributes.contains(&Attribute::TestMain)
                    && self.main_candidate.replace(item).is_some()
                {
                    return Err(CodeErrorKind::MultipleMainFunctions)
                        .with_span_from(&self.scope, node);
                }
            } else if &self.scope.path() == path
                && name == "main"
                && self.main_candidate.replace(item).is_some()
            {
                return Err(CodeErrorKind::MultipleMainFunctions).with_span_from(&self.scope, node);
            }
        }

        let child_scope = self.scope.named_child(ScopeType::Function, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    if self.in_a_container {
                        NamedItemKind::Method(item, node, child_scope.clone())
                    } else {
                        NamedItemKind::Function(item, node, child_scope.clone())
                    },
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
            self.visit_children_by_field(node, "parameters")?;
        });

        Ok(())
    }

    fn visit_type_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);

        let child_scope = self.scope.named_child(ScopeType::Function, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::TypeDef(item, node, child_scope.clone()),
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
        });

        Ok(())
    }

    fn visit_mixin(&mut self, node: Node<'src>) -> Self::ReturnType {
        let attributes = parse_attributes!(self, node);
        let child_scope = self.scope.anonymous_child(ScopeType::Function);

        self.scope
            .add_item(
                None,
                NamedItem::new(NamedItemKind::Mixin(node, child_scope.clone()), attributes),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            if let Some(f) = node.child_by_field_name("type_arguments") {
                self.visit(f)?;
            }
        });

        Ok(())
    }

    fn visit_static_declaration(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);
        self.scope
            .add_item(
                Some(name),
                NamedItem::new(NamedItemKind::Static(item, node), attributes),
            )
            .with_span_from(&self.scope, node)?;

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
                    NamedItem::new_default(NamedItemKind::Placeholder(
                        self.ast.make_id(),
                        argument,
                    )),
                )
                .with_span_from(&self.scope, node)?;
        }

        Ok(())
    }

    fn visit_parameter(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new_default(NamedItemKind::Parameter(self.ast.make_id(), node)),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_macro_parameter(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self.parse_name(node);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new_default(NamedItemKind::MacroParameter(
                    self.ast.make_id(),
                    node.child_by_field_name("et_cetera").is_some(),
                )),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_parameter_list(&mut self, node: Node<'src>) -> Self::ReturnType {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_macro_parameter_list(&mut self, node: Node<'src>) -> Self::ReturnType {
        self.visit_children_by_field(node, "parameter")
    }

    fn visit_use_declaration(&mut self, node: Node<'src>) -> Self::ReturnType {
        let attributes = parse_attributes!(self, node);

        let mut visitor = UseClauseVisitor::new(self.ast, self.scope.clone(), attributes, false);
        visitor.visit(node.child_by_field_name("argument").unwrap())?;

        Ok(())
    }

    fn visit_macro_definition(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);
        let child_scope = self.scope.named_child(ScopeType::Macro, name);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::Macro(item, node, child_scope.clone()),
                    attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        with_child_scope!(self, child_scope, {
            self.visit_children_by_field(node, "parameters")?;
        });

        Ok(())
    }

    fn visit_const_declaration(&mut self, node: Node<'src>) -> Self::ReturnType {
        let item = self.ast.make_symbol();
        let attributes = parse_attributes!(self, node, item);

        let name = self.parse_name(node);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(NamedItemKind::Const(item, node), attributes),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_doc_comment(&mut self, _node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(())
    }

    fn visit_file_doc_comment(&mut self, _node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(())
    }
}
