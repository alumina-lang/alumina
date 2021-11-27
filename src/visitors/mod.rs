use crate::common::SyntaxError;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::Scope;
use crate::AluminaVisitor;

pub mod pass1;
pub mod types;

struct ScopedPathVisitor<'tcx> {
    source: &'tcx str,
    scope: Scope<'tcx>, // global_ctx: &'tcx GlobalCtx<'tcx>
}

impl<'tcx> AluminaVisitor<'tcx> for ScopedPathVisitor<'tcx> {
    type ReturnType = Result<Path<'tcx>, SyntaxError<'tcx>>;

    fn visit_crate(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_crate()
            .ok_or(SyntaxError("crate not allowed", node))?
            .path())
    }

    fn visit_super(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        Ok(self
            .scope
            .find_super()
            .ok_or(SyntaxError("super not allowed", node))?
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
