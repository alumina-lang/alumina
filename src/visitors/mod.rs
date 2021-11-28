use crate::common::{AluminaError, SyntaxError, ToSyntaxError};
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::Scope;
use crate::AluminaVisitor;

pub mod pass1;
pub mod types;

struct ScopedPathVisitor<'tcx> {
    source: &'tcx str,
    scope: Scope<'tcx>, // global_ctx: &'tcx GlobalCtx<'tcx>
}

impl<'tcx> ScopedPathVisitor<'tcx> {
    fn new(source: &'tcx str, scope: Scope<'tcx>) -> Self {
        Self { source, scope }
    }
}

trait VisitorExt<'tcx> {
    type ReturnType;

    fn visit_children(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType;

    fn visit_children_by_field(
        &mut self,
        node: tree_sitter::Node<'tcx>,
        field: &'static str,
    ) -> Self::ReturnType;
}

impl<'tcx, T, E> VisitorExt<'tcx> for T
where
    T: AluminaVisitor<'tcx, ReturnType = Result<(), E>>,
{
    type ReturnType = Result<(), E>;

    fn visit_children(&mut self, node: tree_sitter::Node<'tcx>) -> Result<(), E> {
        let mut cursor = node.walk();
        for node in node.children(&mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn visit_children_by_field(
        &mut self,
        node: tree_sitter::Node<'tcx>,
        field: &'static str,
    ) -> Result<(), E> {
        let mut cursor = node.walk();
        for node in node.children_by_field_name(field, &mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }
}

impl<'tcx> AluminaVisitor<'tcx> for ScopedPathVisitor<'tcx> {
    type ReturnType = Result<Path<'tcx>, SyntaxError<'tcx>>;

    fn visit_crate(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_crate()
            .ok_or(AluminaError::CrateNotAllowed)
            .to_syntax_error(node)?
            .path())
    }

    fn visit_super(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_super()
            .ok_or(AluminaError::SuperNotAllowed)
            .to_syntax_error(node)?
            .path())
    }

    fn visit_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let name = &self.source[node.byte_range()];

        Ok(PathSegment(name).into())
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let name = &self.source[node.byte_range()];

        Ok(PathSegment(name).into())
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let subpath = match node.child_by_field_name("path") {
            Some(subnode) => self.visit(subnode)?,
            None => Path::root(),
        };

        let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];

        Ok(subpath.extend(PathSegment(name)))
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let subpath = self.visit(node.child_by_field_name("path").unwrap())?;
        let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];

        Ok(subpath.extend(PathSegment(name)))
    }
}
