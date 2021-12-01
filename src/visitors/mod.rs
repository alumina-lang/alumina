use tree_sitter::Node;

use crate::common::{AluminaError, SyntaxError, ToSyntaxError};
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::{Item, Scope};
use crate::parser::ParseCtx;
use crate::AluminaVisitor;

pub mod expressions;
pub mod maker;
pub mod pass1;
pub mod types;

struct ScopedPathVisitor<'gcx, 'src> {
    parse_ctx: ParseCtx<'gcx, 'src>,
    scope: Scope<'gcx, 'src>, // global_ctx: &'gcx GlobalCtx<'gcx>
}

impl<'gcx, 'src> ScopedPathVisitor<'gcx, 'src> {
    fn new(scope: Scope<'gcx, 'src>) -> Self {
        Self {
            parse_ctx: scope
                .parse_ctx()
                .expect("cannot run on scope without parse context"),
            scope,
        }
    }
}

trait VisitorExt<'src> {
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

impl<'gcx, 'src> AluminaVisitor<'src> for ScopedPathVisitor<'gcx, 'src> {
    type ReturnType = Result<Path<'src>, SyntaxError<'src>>;

    fn visit_crate(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_crate()
            .ok_or(AluminaError::CrateNotAllowed)
            .to_syntax_error(node)?
            .path())
    }

    fn visit_super(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_super()
            .ok_or(AluminaError::SuperNotAllowed)
            .to_syntax_error(node)?
            .path())
    }

    fn visit_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.parse_ctx.node_text(node);

        Ok(PathSegment(name).into())
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.parse_ctx.node_text(node);

        Ok(PathSegment(name).into())
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let subpath = match node.child_by_field_name("path") {
            Some(subnode) => self.visit(subnode)?,
            None => Path::root(),
        };

        let name = self
            .parse_ctx
            .node_text(node.child_by_field_name("name").unwrap());

        Ok(subpath.extend(PathSegment(name)))
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let subpath = self.visit(node.child_by_field_name("path").unwrap())?;
        let name = self
            .parse_ctx
            .node_text(node.child_by_field_name("name").unwrap());

        Ok(subpath.extend(PathSegment(name)))
    }
}

pub struct UseClauseVisitor<'gcx, 'src> {
    parse_ctx: ParseCtx<'gcx, 'src>,
    prefix: Path<'src>,
    scope: Scope<'gcx, 'src>,
}

impl<'gcx, 'src> UseClauseVisitor<'gcx, 'src> {
    pub fn new(scope: Scope<'gcx, 'src>) -> Self {
        Self {
            prefix: Path::default(),
            parse_ctx: scope
                .parse_ctx()
                .expect("cannot run on scope without parse context"),
            scope,
        }
    }

    fn parse_use_path(&mut self, node: Node<'src>) -> Result<Path<'src>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.scope.clone());
        visitor.visit(node)
    }
}

impl<'gcx, 'src> AluminaVisitor<'src> for UseClauseVisitor<'gcx, 'src> {
    type ReturnType = Result<(), SyntaxError<'src>>;

    fn visit_use_as_clause(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let alias = self
            .parse_ctx
            .node_text(node.child_by_field_name("alias").unwrap());
        self.scope
            .add_item(alias, Item::Alias(self.prefix.join_with(path)))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_use_list(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        self.visit_children_by_field(node, "item")
    }

    fn visit_scoped_use_list(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let suffix = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let new_prefix = self.prefix.join_with(suffix);
        let old_prefix = std::mem::replace(&mut self.prefix, new_prefix);

        self.visit(node.child_by_field_name("list").unwrap())?;
        self.prefix = old_prefix;

        Ok(())
    }

    fn visit_identifier(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let alias = self.parse_ctx.node_text(node);
        self.scope
            .add_item(alias, Item::Alias(self.prefix.extend(PathSegment(alias))))
            .to_syntax_error(node)?;

        Ok(())
    }

    fn visit_scoped_identifier(&mut self, node: Node<'src>) -> Result<(), SyntaxError<'src>> {
        let path = self.parse_use_path(node.child_by_field_name("path").unwrap())?;
        let name = self
            .parse_ctx
            .node_text(node.child_by_field_name("name").unwrap());
        self.scope
            .add_item(
                name,
                Item::Alias(self.prefix.join_with(path.extend(PathSegment(name)))),
            )
            .to_syntax_error(node)?;

        Ok(())
    }
}
