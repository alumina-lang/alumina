use tree_sitter::Node;

use crate::ast::expressions::parse_string_literal;
use crate::ast::{AstCtx, Attribute, ItemP};
use crate::common::{AluminaError, ArenaAllocatable, CodeErrorKind, WithSpanDuringParsing};

use crate::global_ctx::GlobalCtx;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::{NamedItem, NamedItemKind, Scope};
use crate::parser::AluminaVisitor;
use crate::parser::ParseCtx;

pub struct ScopedPathVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>, // ast: &'ast AstCtx<'ast>
    in_a_macro: bool,
}

impl<'ast, 'src> ScopedPathVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>, in_a_macro: bool) -> Self {
        Self {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            in_a_macro,
        }
    }
}

pub trait VisitorExt<'src> {
    type ReturnType;

    fn visit_children(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType;

    fn visit_children_by_field(
        &mut self,
        node: tree_sitter::Node<'src>,
        field: &'static str,
    ) -> Self::ReturnType;
}

impl<'src, T, E> VisitorExt<'src> for T
where
    T: AluminaVisitor<'src, ReturnType = Result<(), E>>,
{
    type ReturnType = Result<(), E>;

    fn visit_children(&mut self, node: tree_sitter::Node<'src>) -> Result<(), E> {
        let mut cursor = node.walk();
        for node in node.children(&mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn visit_children_by_field(
        &mut self,
        node: tree_sitter::Node<'src>,
        field: &'static str,
    ) -> Result<(), E> {
        let mut cursor = node.walk();
        for node in node.children_by_field_name(field, &mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for ScopedPathVisitor<'ast, 'src> {
    type ReturnType = Result<Path<'ast>, AluminaError>;

    fn visit_super(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_super()
            .ok_or(CodeErrorKind::SuperNotAllowed)
            .with_span(&self.scope, node)?
            .path())
    }

    fn visit_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.code.node_text(node).alloc_on(self.ast);

        Ok(PathSegment(name).into())
    }

    fn visit_macro_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_macro {
            return Err(CodeErrorKind::DollaredOutsideOfMacro).with_span(&self.scope, node);
        }

        let name = self.code.node_text(node).alloc_on(self.ast);

        Ok(PathSegment(name).into())
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.code.node_text(node).alloc_on(self.ast);

        Ok(PathSegment(name).into())
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let subpath = match node.child_by_field_name("path") {
            Some(subnode) => self.visit(subnode)?,
            None => Path::root(),
        };

        let name = self
            .code
            .node_text(node.child_by_field_name("name").unwrap())
            .alloc_on(self.ast);

        Ok(subpath.extend(PathSegment(name)))
    }

    fn visit_generic_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        return Err(CodeErrorKind::GenericArgsInPath).with_span(&self.scope, node);
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let subpath = match node.child_by_field_name("path") {
            Some(subnode) => self.visit(subnode)?,
            None => Path::root(),
        };

        let name = self
            .code
            .node_text(node.child_by_field_name("name").unwrap())
            .alloc_on(self.ast);

        Ok(subpath.extend(PathSegment(name)))
    }
}

pub struct UseClauseVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    prefix: Path<'ast>,
    scope: Scope<'ast, 'src>,
    attributes: &'ast [Attribute],
    in_a_macro: bool,
}

impl<'ast, 'src> UseClauseVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        attributes: &'ast [Attribute],
        in_a_macro: bool,
    ) -> Self {
        Self {
            ast,
            prefix: Path::default(),
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            attributes,
            in_a_macro,
        }
    }

    fn parse_use_path(&mut self, node: Node<'src>) -> Result<Path<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);
        visitor.visit(node)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for UseClauseVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_use_as_clause(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let alias = self
            .code
            .node_text(node.child_by_field_name("alias").unwrap())
            .alloc_on(self.ast);

        self.scope
            .add_item(
                Some(alias),
                NamedItem::new(
                    NamedItemKind::Alias(self.prefix.join_with(path)),
                    self.attributes,
                ),
            )
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_use_list(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        self.visit_children_by_field(node, "item")
    }

    fn visit_scoped_use_list(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let suffix = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let new_prefix = self.prefix.join_with(suffix);
        let old_prefix = std::mem::replace(&mut self.prefix, new_prefix);

        self.visit(node.child_by_field_name("list").unwrap())?;
        self.prefix = old_prefix;

        Ok(())
    }

    fn visit_identifier(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let alias = self.code.node_text(node).alloc_on(self.ast);
        self.scope
            .add_item(
                Some(alias),
                NamedItem::new(
                    NamedItemKind::Alias(self.prefix.extend(PathSegment(alias))),
                    self.attributes,
                ),
            )
            .with_span(&self.scope, node)?;

        Ok(())
    }

    fn visit_scoped_identifier(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let path = match node.child_by_field_name("path") {
            Some(path) => self.parse_use_path(path)?,
            None => Path::root(),
        };
        let name = self
            .code
            .node_text(node.child_by_field_name("name").unwrap())
            .alloc_on(self.ast);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::Alias(self.prefix.join_with(path.extend(PathSegment(name)))),
                    self.attributes,
                ),
            )
            .with_span(&self.scope, node)?;

        Ok(())
    }
}

pub struct AttributeVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    item: Option<ItemP<'ast>>,
    attributes: Vec<Attribute>,
    should_skip: bool,
}

impl<'ast, 'src> AttributeVisitor<'ast, 'src> {
    pub fn parse_attributes(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        node: Node<'src>,
        item: Option<ItemP<'ast>>,
    ) -> Result<Option<&'ast [Attribute]>, AluminaError> {
        let mut visitor = AttributeVisitor {
            global_ctx,
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            item,
            attributes: Vec::new(),
            should_skip: false,
        };

        if let Some(node) = node.child_by_field_name("attributes") {
            visitor.visit(node)?;
        }

        if visitor.should_skip {
            Ok(None)
        } else {
            Ok(Some(visitor.attributes.alloc_on(ast)))
        }
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for AttributeVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_attributes(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_children(node)
    }

    fn visit_attribute_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        let inner = node.child_by_field_name("inner").unwrap();

        let name = self
            .code
            .node_text(inner.child_by_field_name("name").unwrap());

        match name {
            "inline" => self.attributes.push(Attribute::Inline),
            "builtin" => self.attributes.push(Attribute::Builtin),
            "export" => self.attributes.push(Attribute::Export),
            "force_inline" => self.attributes.push(Attribute::ForceInline),
            "cfg" => {
                let mut cfg_visitor = CfgVisitor::new(self.global_ctx.clone(), self.scope.clone());
                if !cfg_visitor.visit(inner)? {
                    self.should_skip = true;
                }
            }
            "lang" => {
                let lang_type = inner
                    .child_by_field_name("arguments")
                    .and_then(|n| n.child_by_field_name("argument"))
                    .ok_or(CodeErrorKind::UnknownLangItem(None))
                    .with_span(&self.scope, inner)?;

                self.ast.add_lang_item(
                    self.code
                        .node_text(lang_type)
                        .try_into()
                        .with_span(&self.scope, inner)?,
                    self.item
                        .ok_or(CodeErrorKind::CannotBeALangItem)
                        .with_span(&self.scope, inner)?,
                );
            }
            _ => {}
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
enum State {
    Single,
    All,
    Any,
    Not,
}

pub struct CfgVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    state: Vec<State>,
}

impl<'ast, 'src> CfgVisitor<'ast, 'src> {
    pub fn new(global_ctx: GlobalCtx, scope: Scope<'ast, 'src>) -> Self {
        CfgVisitor {
            global_ctx,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            state: vec![],
        }
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for CfgVisitor<'ast, 'src> {
    type ReturnType = Result<bool, AluminaError>;

    fn visit_meta_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self
            .code
            .node_text(node.child_by_field_name("name").unwrap());

        if let Some(arguments) = node.child_by_field_name("arguments") {
            let ret = match name {
                "cfg" => {
                    self.state.push(State::Single);
                    self.visit(arguments)?
                }
                "all" => {
                    self.state.push(State::All);
                    self.visit(arguments)?
                }
                "any" => {
                    self.state.push(State::Any);
                    self.visit(arguments)?
                }
                "not" => {
                    self.state.push(State::Not);
                    self.visit(arguments)?
                }
                _ => return Err(CodeErrorKind::InvalidCfgAttribute).with_span(&self.scope, node),
            };
            self.state.pop();
            Ok(ret)
        } else {
            let expected = node
                .child_by_field_name("value")
                .map(|n| self.code.node_text(n))
                .map(|s| parse_string_literal(s))
                .transpose()
                .with_span(&self.scope, node)?;

            let actual = self.global_ctx.cfg(name);

            let matches = match (expected, actual) {
                (Some(value), Some(Some(cfg))) => cfg == value,
                (Some(_), Some(None)) => false,
                (None, Some(_)) => true,
                (_, None) => false,
            };

            Ok(matches)
        }
    }

    fn visit_meta_arguments(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let state = *self.state.last().unwrap();
        let mut iter = node.children_by_field_name("argument", &mut cursor);

        while let Some(child) = iter.next() {
            let matches = self.visit(child)?;
            match state {
                State::Single | State::Not => {
                    if iter.next().is_some() {
                        return Err(CodeErrorKind::InvalidCfgAttribute)
                            .with_span(&self.scope, node);
                    }
                    return Ok(matches == matches!(state, State::Single));
                }
                State::All => {
                    if !matches {
                        return Ok(false);
                    }
                }
                State::Any => {
                    if matches {
                        return Ok(true);
                    }
                }
            }
        }

        match state {
            State::Single | State::Not => {
                Err(CodeErrorKind::InvalidCfgAttribute).with_span(&self.scope, node)
            }
            State::All => Ok(true),
            State::Any => Ok(false),
        }
    }
}
