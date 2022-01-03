use tree_sitter::Node;

use crate::ast::lang::LangItemKind;
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
}

impl<'ast, 'src> ScopedPathVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        Self {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
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
        let subpath = self.visit(node.child_by_field_name("path").unwrap())?;
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
    attributes: Vec<Attribute>,
}

impl<'ast, 'src> UseClauseVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        attributes: Vec<Attribute>,
    ) -> Self {
        Self {
            ast,
            prefix: Path::default(),
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            attributes,
        }
    }

    fn parse_use_path(&mut self, node: Node<'src>) -> Result<Path<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone());
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
                    self.attributes.clone(),
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
                    self.attributes.clone(),
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
                    self.attributes.clone(),
                ),
            )
            .with_span(&self.scope, node)?;

        Ok(())
    }
}

pub struct AttributeVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    item: Option<ItemP<'ast>>,
    attributes: Vec<Attribute>,
    should_skip: bool,
}

impl<'ast, 'src> AttributeVisitor<'ast, 'src> {
    pub fn parse_attributes(
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        node: Node<'src>,
        item: Option<ItemP<'ast>>,
    ) -> Result<Option<Vec<Attribute>>, AluminaError> {
        let mut visitor = AttributeVisitor {
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
            Ok(Some(visitor.attributes))
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

/*
fn should_include<'src>(
    global_ctx: &GlobalCtx,
    code: &'src ParseCtx<'src>,
    node: tree_sitter::Node<'src>,
) -> Result<bool, AluminaError> {
    let attribute_node = match node.child_by_field_name("attributes") {
        Some(node) => node,
        None => return Ok(true),
    };

    let cfg_regex = Regex::new(r"^\s*cfg\s*\(.*\)").unwrap();

    let mut cursor = attribute_node.walk();
    let result = attribute_node
        .children(&mut cursor)
        .map(|n| code.node_text(n.child_by_field_name("name").unwrap()))
        .filter(|s| match lang_item_kind(s) {
            Some(kind) => {
                // We allow lang items to be overriden.
                self.lang_items.insert(kind, item);
                false
            }
            None => true,
        })
        .filter_map(|name| match name {
            "export" => Some(Attribute::Export),
            "inline" => Some(Attribute::Inline),
            "force_inline" => Some(Attribute::ForceInline),
            _ => None,
        })
        .collect::<Vec<_>>()
        .alloc_on(self.ast);

    Ok(result)
}
*/
