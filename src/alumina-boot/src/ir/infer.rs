use super::{
    lang::LangTypeKind,
    mono::{MonoCtx, Monomorphizer},
    UnqualifiedKind,
};
use crate::{
    ast::{self, lang::LangItemKind, rebind::Rebinder, BuiltinType, Placeholder},
    ir,
};
use std::collections::HashMap;

pub struct TypeInferer<'a, 'ast, 'ir> {
    ast: &'ast ast::AstCtx<'ast>,
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    placeholders: Vec<ast::Placeholder<'ast>>,
}

impl<'a, 'ast, 'ir> TypeInferer<'a, 'ast, 'ir> {
    pub fn new(
        ast: &'ast ast::AstCtx<'ast>,
        mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
        placeholders: Vec<ast::Placeholder<'ast>>,
    ) -> Self {
        TypeInferer {
            ast,
            mono_ctx,
            placeholders,
        }
    }

    fn match_slot(
        &mut self,
        inferred: &mut HashMap<ast::AstId, ir::TyP<'ir>>,
        src: ast::TyP<'ast>,
        tgt: ir::TyP<'ir>,
    ) -> Result<(), ()> {
        match (src, tgt) {
            (ast::Ty::NamedFunction(_), _)
            | (ast::Ty::NamedType(_), _)
            | (ast::Ty::Builtin(_), _) => {
                // those do not participate in inference
            }
            (ast::Ty::Placeholder(id), _) => {
                let tgt = if let ir::Ty::Unqualified(UnqualifiedKind::String(_)) = tgt {
                    // Unqualified types cannot be named explicitely, so it is almost certainly not
                    // the right choice for inference. Use the type it coerces into instead.
                    // TODO: This is ugly and bad, get rid of unqualified types altogether.
                    let mut monomorphizer = Monomorphizer::new(self.mono_ctx, true, None);
                    monomorphizer.try_qualify_type(tgt).unwrap()
                } else {
                    tgt
                };

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
            (ast::Ty::FunctionPointer(a1, a2), ir::Ty::FunctionPointer(b1, b2)) => {
                for (a, b) in a1.iter().zip(b1.iter()) {
                    self.match_slot(inferred, a, b)?;
                }
                self.match_slot(inferred, a2, b2)?;
            }
            (ast::Ty::FunctionPointer(a1, a2), ir::Ty::NamedFunction(item)) => {
                if let Ok(fun) = item.get_function() {
                    for (a, b) in a1.iter().zip(fun.args.iter()) {
                        self.match_slot(inferred, a, b.ty)?;
                    }
                    self.match_slot(inferred, a2, fun.return_type)?;
                }
            }
            (ast::Ty::Generic(item, holders), ir::Ty::NamedType(t) | ir::Ty::NamedFunction(t)) => {
                if let ast::Item::TypeDef(t) = item.get() {
                    let mut rebinder = Rebinder::new(
                        self.ast,
                        t.placeholders
                            .iter()
                            .map(|h| h.id)
                            .zip(holders.iter().copied())
                            .collect(),
                    );

                    if let Ok(src) = rebinder.visit_typ(t.target) {
                        return self.match_slot(inferred, src, tgt);
                    }
                }

                let mono_key = self.mono_ctx.reverse_lookup(t);
                if mono_key.0 != *item {
                    return Err(());
                }

                for (holder, t) in holders.iter().zip(mono_key.1.iter()) {
                    self.match_slot(inferred, *holder, *t)?;
                }
            }
            (ast::Ty::Dyn(ast::Ty::Generic(item, holders), a_const), _) => {
                if let Some(LangTypeKind::Dyn(
                    ir::Ty::Protocol(proto),
                    ir::Ty::Pointer(_, b_const),
                )) = self.mono_ctx.get_lang_type_kind(tgt)
                {
                    if !*a_const && (*a_const != *b_const) {
                        return Err(());
                    }

                    let mono_key = self.mono_ctx.reverse_lookup(proto);
                    if mono_key.0 != *item {
                        return Err(());
                    }

                    for (holder, t) in holders.iter().zip(mono_key.1.iter().skip(1)) {
                        self.match_slot(inferred, *holder, *t)?;
                    }
                } else {
                    return Err(());
                }
            }
            _ => return Err(()),
        }

        Ok(())
    }

    fn match_protocol_bounds(
        &mut self,
        inferred: &mut HashMap<ast::AstId, ir::TyP<'ir>>,
        placeholder: &Placeholder<'ast>,
    ) {
        // Matching protocol bounds is quite limited at the moment, it only works for certain
        // builtin protocols and even there it only works in the reverse direction, e.g. if
        // we have <A, B, C, F: Callable<(A, B), C>> and F is a known function/function pointer,
        // we can infer A, B and C.
        if let Some(tgt) = inferred.get(&placeholder.id).copied() {
            for bound in placeholder.bounds {
                let (item, args) = match bound.typ {
                    ast::Ty::Generic(item, args) => (item, args),
                    _ => continue,
                };

                match self.ast.lang_item_kind(item) {
                    Some(LangItemKind::ProtoArrayOf) => {
                        if let [src] = args {
                            if let ir::Ty::Array(tgt, _) = tgt {
                                let _ = self.match_slot(inferred, src, tgt);
                            }
                        }
                    }
                    Some(LangItemKind::ProtoPointerOf) => {
                        if let [src] = args {
                            if let ir::Ty::Pointer(tgt, _) = tgt {
                                let _ = self.match_slot(inferred, src, tgt);
                            }
                        }
                    }
                    Some(LangItemKind::ProtoRangeOf) => {
                        if let [src] = args {
                            if let Some(LangTypeKind::Range(inner)) =
                                self.mono_ctx.get_lang_type_kind(tgt)
                            {
                                let _ = self.match_slot(inferred, src, inner);
                            }
                        }
                    }
                    Some(LangItemKind::ProtoCallable) => match args {
                        [ast::Ty::Tuple(a1), a2] => match tgt {
                            ir::Ty::FunctionPointer(b1, b2) => {
                                for (a, b) in a1.iter().zip(b1.iter()) {
                                    let _ = self.match_slot(inferred, a, b);
                                }
                                let _ = self.match_slot(inferred, a2, b2);
                            }
                            ir::Ty::NamedFunction(item) => {
                                if let Ok(fun) = item.get_function() {
                                    for (a, b) in a1.iter().zip(fun.args.iter()) {
                                        let _ = self.match_slot(inferred, a, b.ty);
                                    }
                                    let _ = self.match_slot(inferred, a2, fun.return_type);
                                }
                            }
                            ir::Ty::Closure(item) => {
                                if let Ok(clos) = item.get_closure() {
                                    if let Ok(fun) = clos.function.get().unwrap().get_function() {
                                        for (a, b) in a1.iter().zip(fun.args.iter().skip(1)) {
                                            let _ = self.match_slot(inferred, a, b.ty);
                                        }
                                        let _ = self.match_slot(inferred, a2, fun.return_type);
                                    }
                                }
                            }
                            _ => {}
                        },
                        [ast::Ty::Builtin(BuiltinType::Void), a2] => match tgt {
                            ir::Ty::FunctionPointer(_, b2) => {
                                let _ = self.match_slot(inferred, a2, b2);
                            }
                            ir::Ty::NamedFunction(item) => {
                                if let Ok(fun) = item.get_function() {
                                    let _ = self.match_slot(inferred, a2, fun.return_type);
                                }
                            }
                            ir::Ty::Closure(item) => {
                                if let Ok(clos) = item.get_closure() {
                                    if let Ok(fun) = clos.function.get().unwrap().get_function() {
                                        let _ = self.match_slot(inferred, a2, fun.return_type);
                                    }
                                }
                            }
                            _ => {}
                        },
                        _ => {}
                    },
                    _ => {}
                }
            }
        }
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

        let placeholders: Vec<_> = self.placeholders.to_vec();
        for placeholder in placeholders {
            self.match_protocol_bounds(&mut inferred, &placeholder)
        }

        let mut defaults_only = false;
        let mut result = Vec::new();
        for placeholder in self.placeholders.iter() {
            if let Some(ty) = inferred.get(&placeholder.id) {
                if defaults_only {
                    return None;
                }
                result.push(*ty);
            } else if placeholder.default.is_some() {
                defaults_only = true;
            } else {
                return None;
            }
        }

        Some(result)
    }
}
