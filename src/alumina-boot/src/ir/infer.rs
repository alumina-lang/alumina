use crate::ast::lang::Lang;
use crate::ast::rebind::Rebinder;
use crate::ast::Placeholder;
use crate::common::HashMap;
use crate::ir::mono::MonoCtx;
use crate::{ast, ir};

use super::builder::TypeBuilder;
use super::LangKind;

pub struct TypeInferer<'a, 'ast, 'ir> {
    ast: &'ast ast::AstCtx<'ast>,
    types: TypeBuilder<'ir>,
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    placeholders: Vec<ast::Placeholder<'ast>>,
}

impl<'a, 'ast, 'ir> TypeInferer<'a, 'ast, 'ir> {
    pub fn new(
        ast: &'ast ast::AstCtx<'ast>,
        ir: &'ir ir::IrCtx<'ir>,
        mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
        placeholders: Vec<ast::Placeholder<'ast>>,
    ) -> Self {
        TypeInferer {
            ast,
            types: TypeBuilder::new(ir),
            mono_ctx,
            placeholders,
        }
    }

    fn match_slot(
        &mut self,
        inferred: &mut HashMap<ast::Id, ir::TyP<'ir>>,
        src: ast::TyP<'ast>,
        tgt: ir::TyP<'ir>,
    ) -> Result<(), ()> {
        if let ast::Ty::Tag(_, inner) = src {
            return self.match_slot(inferred, inner, tgt);
        }

        match (src, tgt) {
            (ast::Ty::Item(_), _) | (ast::Ty::Builtin(_), _) => {
                // those do not participate in inference
            }
            (ast::Ty::Placeholder(id), _) => {
                if let Some(existing) = inferred.get(id) {
                    if *existing != tgt {
                        return Err(());
                    }
                } else {
                    inferred.entry(*id).or_insert(tgt);
                }
            }
            (ast::Ty::Pointer(a1, a_const), ir::Ty::Pointer(b1, b_const)) => {
                // mut pointers coerce into const pointers
                if !a_const && (a_const != b_const) {
                    return Err(());
                }
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Array(a1, _), ir::Ty::Array(b1, _)) => {
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Slice(a1, a_const), ir::Ty::Item(_t)) => {
                let lang_item_kind = self.mono_ctx.lang_type_kind(tgt);
                if let Some(LangKind::Slice(ir::Ty::Pointer(b1, b_const))) = lang_item_kind {
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
            (ast::Ty::FunctionPointer(a1, a2), ir::Ty::Item(item)) => match item.get() {
                Ok(ir::Item::Function(fun)) => {
                    for (a, b) in a1.iter().zip(fun.args.iter()) {
                        self.match_slot(inferred, a, b.ty)?;
                    }
                    self.match_slot(inferred, a2, fun.return_type)?;
                }
                _ => return Err(()),
            },
            (ast::Ty::Generic(inner, holders), ir::Ty::Item(t)) => {
                let item = match inner {
                    ast::Ty::Item(item) => item,
                    _ => return Err(()),
                };

                if let ast::Item::TypeDef(ast::TypeDef {
                    placeholders,
                    target: Some(target),
                    ..
                }) = item.get()
                {
                    let mut rebinder = Rebinder::new(
                        self.ast,
                        placeholders
                            .iter()
                            .map(|h| h.id)
                            .zip(holders.iter().copied())
                            .collect(),
                    );

                    if let Ok(src) = rebinder.visit_ty(target) {
                        return self.match_slot(inferred, src, tgt);
                    }
                }

                let mono_key = self.mono_ctx.reverse_lookup(t);
                if mono_key.0 != *item {
                    return Err(());
                }

                for (holder, t) in holders.iter().zip(mono_key.1.iter()) {
                    self.match_slot(inferred, holder, t)?;
                }
            }
            (ast::Ty::Dyn(a_protos, a_const), _) => {
                if let Some(LangKind::Dyn(ir::Ty::Tuple(b_protos), ir::Ty::Pointer(_, b_const))) =
                    self.mono_ctx.lang_type_kind(tgt)
                {
                    for (a_ty, b_ty) in a_protos.iter().zip(b_protos.iter()) {
                        let (item, holders) = match a_ty {
                            ast::Ty::Generic(ast::Ty::Item(item), holders) => (item, holders),
                            _ => return Err(()),
                        };

                        let proto = match b_ty {
                            ir::Ty::Item(proto) => proto,
                            _ => return Err(()),
                        };

                        if !*a_const && (*a_const != *b_const) {
                            return Err(());
                        }

                        let mono_key = self.mono_ctx.reverse_lookup(proto);
                        if mono_key.0 != *item {
                            return Err(());
                        }

                        for (holder, t) in holders.iter().zip(mono_key.1.iter()) {
                            self.match_slot(inferred, holder, t)?;
                        }
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
        inferred: &mut HashMap<ast::Id, ir::TyP<'ir>>,
        placeholder: &Placeholder<'ast>,
    ) {
        // Matching protocol bounds is quite limited at the moment, it only works for certain
        // builtin protocols and even there it only works in the reverse direction, e.g. if
        // we have <A, B, C, F: Fn(A, B) -> C> and F is a known function/function pointer,
        // we can infer A, B and C.
        if let Some(tgt) = inferred.get(&placeholder.id).copied() {
            if placeholder.bounds.kind == ast::ProtocolBoundsKind::Any {
                return;
            }

            for bound in placeholder.bounds.bounds {
                let (item, args) = match bound.ty {
                    ast::Ty::Generic(ast::Ty::Item(item), args) => (item, args),
                    // Special case for Fn(A...) -> B
                    ast::Ty::FunctionProtocol([ast::Ty::EtCetera(tup)], ret) => {
                        self.match_callable(inferred, tgt, tup, ret);
                        continue;
                    }
                    ast::Ty::FunctionProtocol(args, ret) => {
                        let tup = self.ast.intern_type(ast::Ty::Tuple(args));
                        self.match_callable(inferred, tgt, tup, ret);
                        continue;
                    }
                    _ => continue,
                };

                match self.ast.lang_item_kind(item) {
                    Some(Lang::ProtoArrayOf) => {
                        if let [src] = args {
                            if let ir::Ty::Array(tgt, _) = tgt {
                                let _ = self.match_slot(inferred, src, tgt);
                            }
                        }
                    }
                    Some(Lang::ProtoPointerOf) => {
                        if let [src] = args {
                            if let ir::Ty::Pointer(tgt, _) = tgt {
                                let _ = self.match_slot(inferred, src, tgt);
                            }
                        }
                    }
                    Some(Lang::ProtoRangeOf) => {
                        if let [src] = args {
                            if let Some(LangKind::Range(inner, _)) =
                                self.mono_ctx.lang_type_kind(tgt)
                            {
                                let _ = self.match_slot(inferred, src, inner);
                            }
                        }
                    }
                    Some(Lang::ProtoCallable) => match args {
                        [a1, a2] => self.match_callable(inferred, tgt, a1, a2),
                        _ => {}
                    },
                    _ => {}
                }
            }
        }
    }

    fn match_callable(
        &mut self,
        inferred: &mut HashMap<ast::Id, ir::TyP<'ir>>,
        tgt: ir::TyP<'ir>,
        ast_args: ast::TyP<'ast>,
        ast_ret: ast::TyP<'ast>,
    ) {
        match tgt {
            ir::Ty::FunctionPointer(b1, b2) => {
                let tup = self.types.tuple(b1.iter().copied());
                let _ = self.match_slot(inferred, ast_args, tup);
                let _ = self.match_slot(inferred, ast_ret, b2);
            }
            ir::Ty::Item(item) => match item.get() {
                Ok(ir::Item::Closure(clos)) => {
                    if let Ok(fun) = clos.function.get().unwrap().get_function() {
                        let tup = self.types.tuple(fun.args.iter().skip(1).map(|a| a.ty));
                        let _ = self.match_slot(inferred, ast_args, tup);
                        let _ = self.match_slot(inferred, ast_ret, fun.return_type);
                    }
                }
                Ok(ir::Item::Function(fun)) => {
                    let tup = self.types.tuple(fun.args.iter().map(|a| a.ty));
                    let _ = self.match_slot(inferred, ast_args, tup);
                    let _ = self.match_slot(inferred, ast_ret, fun.return_type);
                }
                _ => {}
            },
            _ => {}
        }
    }

    pub fn try_infer(
        &mut self,
        self_slot: Option<(ast::TyP<'ast>, ir::TyP<'ir>)>,
        pairs: impl IntoIterator<Item = (ast::TyP<'ast>, ir::TyP<'ir>)>,
    ) -> Option<Vec<ir::TyP<'ir>>> {
        let mut inferred = HashMap::default();

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
