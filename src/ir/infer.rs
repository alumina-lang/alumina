use std::collections::HashMap;
use crate::{ast, ir};
use super::mono::{MonoCtx, MonomorphizeKey};


pub struct TypeInferer<'a, 'ast, 'ir> {
    mono_ctx: &'a MonoCtx<'ast, 'ir>,
    placeholders: Vec<ast::AstId>,
}

impl<'a, 'ast, 'ir> TypeInferer<'a, 'ast, 'ir> {
    pub fn new(mono_ctx: &'a MonoCtx<'ast, 'ir>, placeholders: Vec<ast::AstId>) -> Self {
        TypeInferer {
            mono_ctx,
            placeholders,
        }
    }

    fn match_slot(
        &self,
        inferred: &mut HashMap<ast::AstId, ir::TyP<'ir>>,
        src: ast::TyP<'ast>,
        tgt: ir::TyP<'ir>,
    ) -> Result<(), ()> {
        match (src, tgt) {
            (ast::Ty::Extern(_), _) | (ast::Ty::NamedType(_), _) | (ast::Ty::Builtin(_), _) => {
                // those do not participate in inference
            }
            (ast::Ty::Placeholder(id), _) => {
                if inferred.len() == self.placeholders.len() {
                    return Err(());
                }
                inferred.insert(*id, tgt);
            }
            (ast::Ty::Pointer(a1, a2), ir::Ty::Pointer(b1, b2)) => {
                if a2 != b2 {
                    return Err(());
                }
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Array(a1, a2), ir::Ty::Array(b1, b2)) => {
                if a2 != b2 {
                    return Err(());
                }
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Slice(a), ir::Ty::Slice(b)) => self.match_slot(inferred, a, b)?,
            (ast::Ty::Tuple(a), ir::Ty::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(());
                }
                for (a, b) in a.iter().zip(b.iter()) {
                    self.match_slot(inferred, a, b)?;
                }
            }
            (ast::Ty::Function(a1, a2), ir::Ty::Fn(b1, b2)) => {
                for (a, b) in a1.iter().zip(b1.iter()) {
                    self.match_slot(inferred, a, b)?;
                }
                self.match_slot(inferred, a2, b2)?;
            }
            (ast::Ty::GenericType(item, holders), ir::Ty::NamedType(t)) => {
                let mono_key = self.mono_ctx.reverse_lookup(t);
                if mono_key.0 != *item {
                    return Err(());
                }

                for (holder, t) in holders.iter().zip(mono_key.1.iter()) {
                    self.match_slot(inferred, *holder, *t)?;
                }
            }
            _ => return Err(()),
        }

        Ok(())
    }

    pub fn try_infer(
        &mut self,
        self_slot: Option<(ast::TyP<'ast>, ir::TyP<'ir>)>,
        pairs: impl IntoIterator<Item = (ast::TyP<'ast>, ir::TyP<'ir>)>,
    ) -> Option<Vec<ir::TyP<'ir>>> {
        let mut inferred = HashMap::new();

        if let Some((src, tgt)) = self_slot {
            let _ = self.match_slot(&mut inferred, src.canonical_type(), tgt.canonical_type());
        }

        for (param, actual) in pairs {
            let _ = self.match_slot(&mut inferred, param, actual);
        }

        if inferred.len() == self.placeholders.len() {
            Some(self.placeholders.iter().map(|id| inferred[id]).collect())
        } else {
            None
        }
    }
}
