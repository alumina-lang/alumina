use super::{lang::LangTypeKind, mono::MonoCtx};
use crate::{ast, ir};
use std::collections::HashMap;

pub struct TypeInferer<'a, 'ast, 'ir> {
    mono_ctx: &'a MonoCtx<'ast, 'ir>,
    placeholders: Vec<ast::Placeholder<'ast>>,
}

impl<'a, 'ast, 'ir> TypeInferer<'a, 'ast, 'ir> {
    pub fn new(
        mono_ctx: &'a MonoCtx<'ast, 'ir>,
        placeholders: Vec<ast::Placeholder<'ast>>,
    ) -> Self {
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
            (ast::Ty::NamedType(_), _) | (ast::Ty::Builtin(_), _) => {
                // those do not participate in inference
            }
            (ast::Ty::Placeholder(id), _) => {
                if let Some(existing) = inferred.get(id) {
                    if *existing != tgt {
                        return Err(());
                    }
                } else {
                    inferred.insert(*id, tgt);
                }
            }
            (ast::Ty::Pointer(a1, a_const), ir::Ty::Pointer(b1, b_const)) => {
                // mut pointers coerce into const pointers
                if !a_const && (a_const != b_const) {
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
            (ast::Ty::Slice(a1, a_const), ir::Ty::NamedType(_t)) => {
                let lang_item_kind = self.mono_ctx.get_lang_type_kind(tgt);
                if let Some(LangTypeKind::Slice(ir::Ty::Pointer(b1, b_const))) = lang_item_kind {
                    // mut slices coerce into const slices
                    if !a_const && (a_const != b_const) {
                        return Err(());
                    }
                    self.match_slot(inferred, a1, b1)?;
                }

                return Err(());
            }
            // Special case for &[T; size] -> &[T] coercions
            (ast::Ty::Slice(a1, a_const), ir::Ty::Pointer(ir::Ty::Array(b1, _), b_const)) => {
                if !a_const && (a_const != b_const) {
                    return Err(());
                }
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Tuple(a), ir::Ty::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(());
                }
                for (a, b) in a.iter().zip(b.iter()) {
                    self.match_slot(inferred, a, b)?;
                }
            }
            (ast::Ty::Fn(a1, a2), ir::Ty::Fn(b1, b2)) => {
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
            Some(
                self.placeholders
                    .iter()
                    .map(|placeholder| inferred[&placeholder.id])
                    .collect(),
            )
        } else {
            None
        }
    }
}
