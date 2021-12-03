use std::collections::HashSet;

use crate::{ast, common::AluminaError, context::AstCtx, ir};

/*

pub struct Monomorphizer<'ast, 'ir> {
    ctx: &'ast AstCtx<'ast>,
    replacements: HashSet<NodeId, ir::TyP<'ir>>
}

impl<'ast, 'ir> Monomorphizer<'ast, 'ir> {

}

pub fn monomorphize_symbol(&self, placeholders: &[ir::TyP<'ir>]) -> Result<ir::IRItemP, AluminaError> {
    match self.symbol.get() {
        ast::Item::Function(func) => {
            unimplemented!()
        },
        ast::Item::Struct(struct_) => {
            let mut struct_ = struct_.clone();
            struct_.fields = self.ctx.visit_fields(struct_.fields)?;
        }
    }
}

 */
