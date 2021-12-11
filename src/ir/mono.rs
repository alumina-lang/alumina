use core::panic;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use std::iter::{once, repeat};

use super::builder::ExpressionBuilder;
use super::const_eval::{const_eval, numeric_of_kind, Value};
use super::infer::TypeInferer;
use super::lang::LangTypeKind;
use super::optimize::Optimizer;
use super::Lit;
use crate::ast::lang::{LangItemKind, LangItemMap};
use crate::ast::{BuiltinType, Span};
use crate::common::{AddSpan, AluminaError, ArenaAllocatable, WithNoSpan, WithSpan};
use crate::ir::{FuncBodyCell, ValueType};
use crate::{ast, common::AluminaErrorKind, ir};

macro_rules! builtin {
    ($self:expr, $name:ident) => {
        $self
            .mono_ctx
            .ir
            .intern_type(crate::ir::Ty::Builtin(crate::ast::BuiltinType::$name))
    };
}

macro_rules! mismatch {
    ($expected:expr, $actual:expr) => {
        crate::common::AluminaErrorKind::TypeMismatch(
            format!("{:?}", $expected),
            format!("{:?}", $actual),
        )
    };
}

pub struct MonoCtx<'ast, 'ir> {
    ir: &'ir ir::IrCtx<'ir>,
    id_map: HashMap<ast::AstId, ir::IrId>,
    lang_items: LangItemMap<'ast>,
    finished: HashMap<MonomorphizeKey<'ast, 'ir>, ir::IRItemP<'ir>>,
    reverse_map: HashMap<ir::IRItemP<'ir>, MonomorphizeKey<'ast, 'ir>>,
}

impl<'ast, 'ir> MonoCtx<'ast, 'ir> {
    pub fn new(ir: &'ir ir::IrCtx<'ir>, lang_items: LangItemMap<'ast>) -> Self {
        MonoCtx {
            ir,
            id_map: HashMap::new(),
            finished: HashMap::new(),
            reverse_map: HashMap::new(),
            lang_items,
        }
    }

    fn map_id(&mut self, id: ast::AstId) -> ir::IrId {
        *self.id_map.entry(id).or_insert_with(|| self.ir.make_id())
    }

    pub fn reverse_lookup(&self, item: ir::IRItemP<'ir>) -> MonomorphizeKey<'ast, 'ir> {
        self.reverse_map
            .get(&item)
            .cloned()
            .expect("reverse lookup failed")
    }

    pub fn get_lang_type_kind(&self, typ: ir::TyP<'ir>) -> Option<LangTypeKind<'ir>> {
        let item = match typ {
            ir::Ty::NamedType(item) => item,
            _ => return None,
        };

        let item = self.reverse_lookup(item);
        if self.lang_items.get(LangItemKind::Slice).ok() == Some(item.0) {
            return Some(LangTypeKind::Slice(item.1[0]));
        }

        return None;
    }

    pub fn into_inner(self) -> Vec<ir::IRItemP<'ir>> {
        self.finished.values().copied().collect()
    }
}

#[derive(Debug, Clone)]
pub struct LoopContext<'ir> {
    type_hint: Option<ir::TyP<'ir>>,
    loop_result: ir::IrId,
    break_label: ir::IrId,
    continue_label: ir::IrId,
}

pub struct Monomorphizer<'a, 'ast, 'ir> {
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    local_types: HashMap<ir::IrId, ir::TyP<'ir>>,
    return_type: Option<ir::TyP<'ir>>,
    builder: ExpressionBuilder<'ir>,
    loop_contexts: Vec<LoopContext<'ir>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphizeKey<'ast, 'ir>(pub ast::ItemP<'ast>, pub &'ir [ir::TyP<'ir>]);

impl<'a, 'ast, 'ir> Monomorphizer<'a, 'ast, 'ir> {
    pub fn new<'b>(mono_ctx: &'b mut MonoCtx<'ast, 'ir>) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        Monomorphizer {
            mono_ctx,
            replacements: HashMap::new(),
            local_types: HashMap::new(),
            builder: ExpressionBuilder::new(ir),
            return_type: None,
            loop_contexts: Vec::new(),
        }
    }

    pub fn with_replacements<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    ) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        Monomorphizer {
            mono_ctx,
            replacements,
            local_types: HashMap::new(),
            builder: ExpressionBuilder::new(ir),
            return_type: None,
            loop_contexts: Vec::new(),
        }
    }

    pub fn monomorphize(
        &mut self,
        item: ast::ItemP<'ast>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        self.monomorphize_item(MonomorphizeKey(item, &[]))
    }

    pub fn monomorphize_item(
        &mut self,
        key: MonomorphizeKey<'ast, 'ir>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let item: ir::IRItemP = match self.mono_ctx.finished.entry(key.clone()) {
            // The cell may be empty at this point if we are dealing with recursive references
            // In this case, we will just return the item as is, but it will not
            // be populated until the top-level item is finished.
            Entry::Occupied(entry) => return Ok(entry.get()),
            Entry::Vacant(entry) => {
                let symbol = self.mono_ctx.ir.make_symbol();
                self.mono_ctx.reverse_map.insert(symbol, key.clone());
                entry.insert(symbol)
            }
        };

        match key.0.get() {
            ast::Item::Enum(en) => {
                if key.1.len() != 0 {
                    return Err(AluminaErrorKind::GenericParamCountMismatch(0, key.1.len()))
                        .with_no_span();
                }

                let mut members = Vec::new();
                let mut child = Self::new(self.mono_ctx);
                let mut type_hint = None;
                let mut taken_values = HashSet::new();

                let (valued, non_valued): (Vec<_>, Vec<_>) =
                    en.members.iter().copied().partition(|m| m.value.is_some());

                for m in valued {
                    let expr = child.lower_expr(m.value.unwrap(), type_hint)?;
                    let value = const_eval(expr).expect("cannot const evaluate");
                    let value_type = child
                        .mono_ctx
                        .ir
                        .intern_type(ir::Ty::Builtin(value.type_kind()));

                    if !type_hint
                        .get_or_insert(value_type)
                        .assignable_from(value_type)
                    {
                        return Err(mismatch!(type_hint.unwrap(), value_type)).with_span(m.span);
                    }

                    if !taken_values.insert(value) {
                        return Err(AluminaErrorKind::DuplicateEnumMember).with_span(m.span);
                    }

                    members.push(ir::EnumMember {
                        id: child.mono_ctx.map_id(m.id),
                        value: child.builder.const_value(value),
                    });
                }

                // This monstrosity to populate non-valued members with arbitrary types using
                // const-eval. It's bad, but it works.

                let kind = match type_hint.get_or_insert(builtin!(child, I32)) {
                    ir::Ty::Builtin(k) => *k,
                    _ => unreachable!(),
                };

                let mut counter = numeric_of_kind!(kind, 0);
                for m in non_valued {
                    let next_non_taken = loop {
                        if taken_values.insert(counter) {
                            break counter;
                        }
                        counter = const_eval(self.builder.binary(
                            ast::BinOp::Plus,
                            self.builder.const_value(counter),
                            self.builder.const_value(numeric_of_kind!(kind, 1)),
                            type_hint.unwrap(),
                        ))
                        .unwrap();
                    };

                    members.push(ir::EnumMember {
                        id: child.mono_ctx.map_id(m.id),
                        value: self.builder.const_value(next_non_taken),
                    });
                }

                let res = ir::IRItem::Enum(ir::Enum {
                    name: en.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                    underlying_type: type_hint.unwrap(),
                    members: members.alloc_on(child.mono_ctx.ir),
                });

                item.assign(res);
            }
            ast::Item::Function(func) => {
                if key.1.len() != func.placeholders.len() {
                    return Err(AluminaErrorKind::GenericParamCountMismatch(
                        func.placeholders.len(),
                        key.1.len(),
                    ))
                    .with_no_span();
                }

                let mut child = Self::with_replacements(
                    self.mono_ctx,
                    func.placeholders
                        .iter()
                        .zip(key.1.iter())
                        .map(|(&k, &v)| (k, v))
                        .collect(),
                );

                let parameters = func
                    .args
                    .iter()
                    .map(|p| {
                        let param = ir::Parameter {
                            id: child.mono_ctx.map_id(p.id),
                            ty: child.lower_type(p.typ)?,
                        };
                        child.local_types.insert(param.id, param.ty);
                        Ok(param)
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                let return_type = child.lower_type(func.return_type)?;
                let res = ir::IRItem::Function(ir::Function {
                    name: func.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                    attributes: func.attributes.alloc_on(child.mono_ctx.ir),
                    args: &parameters.alloc_on(child.mono_ctx.ir),
                    return_type,
                    body: FuncBodyCell::new(),
                });
                item.assign(res);

                // We need the item to be assigned before we monomorphize the body, as the
                // function can be recursive and we need to be able to get the signature for
                // typechecking purposes.

                child.return_type = Some(return_type);
                if let Some(body) = func.body {
                    child.return_type = Some(return_type);
                    let body = child.lower_expr(body, Some(return_type))?;
                    let body = child.try_coerce(return_type, body)?;

                    let mut optimizer = Optimizer::new(child.mono_ctx.ir);
                    let optimized = optimizer.optimize_func_body(body);

                    item.get_function().body.assign(optimized);
                }
            }
            ast::Item::Struct(s) => {
                if key.1.len() != s.placeholders.len() {
                    return Err(AluminaErrorKind::GenericParamCountMismatch(
                        s.placeholders.len(),
                        key.1.len(),
                    ))
                    .with_no_span();
                }

                let mut child = Self::with_replacements(
                    self.mono_ctx,
                    s.placeholders
                        .iter()
                        .zip(key.1.iter())
                        .map(|(&k, &v)| (k, v))
                        .collect(),
                );

                let fields = s
                    .fields
                    .iter()
                    .map(|f| {
                        Ok(ir::Field {
                            id: child.mono_ctx.map_id(f.id),
                            ty: child.lower_type(f.typ)?,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                let res = ir::IRItem::Struct(ir::Struct {
                    name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                    fields: fields.alloc_on(self.mono_ctx.ir),
                });
                item.assign(res);
            }
        };

        Ok(item)
    }

    pub fn monomorphize_lang_item<I>(
        &mut self,
        kind: LangItemKind,
        generic_args: I,
    ) -> Result<ir::IRItemP<'ir>, AluminaError>
    where
        I: IntoIterator<Item = ir::TyP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let item = self.mono_ctx.lang_items.get(kind).with_no_span()?;
        let args = self.mono_ctx.ir.arena.alloc_slice_fill_iter(generic_args);
        let key = MonomorphizeKey(item, args);

        self.monomorphize_item(key)
    }

    pub fn lower_type(&mut self, typ: ast::TyP<'ast>) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *typ {
            // TODO: can coalesce same usize == u64 depending on platform here I guess
            ast::Ty::Builtin(kind) => ir::Ty::Builtin(kind),
            ast::Ty::Array(inner, len) => ir::Ty::Array(self.lower_type(inner)?, len),
            ast::Ty::Pointer(inner, is_const) => ir::Ty::Pointer(self.lower_type(inner)?, is_const),
            ast::Ty::Slice(inner, is_const) => {
                let ptr_type = self
                    .mono_ctx
                    .ir
                    .intern_type(ir::Ty::Pointer(self.lower_type(inner)?, is_const));
                let item = self.monomorphize_lang_item(LangItemKind::Slice, [ptr_type])?;
                ir::Ty::NamedType(item)
            }
            ast::Ty::Extern(id) => ir::Ty::Extern(self.mono_ctx.map_id(id)),
            ast::Ty::Fn(args, ret) => ir::Ty::Fn(
                args.iter()
                    .map(|arg| self.lower_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir),
                self.lower_type(ret)?,
            ),
            ast::Ty::Tuple(items) => ir::Ty::Tuple(
                items
                    .iter()
                    .map(|arg| self.lower_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir),
            ),

            ast::Ty::Placeholder(id) => *self
                .replacements
                .get(&id)
                .copied()
                .expect("unbound placeholder"),

            ast::Ty::NamedType(item) => {
                let key = MonomorphizeKey(item, &[]);
                let item = self.monomorphize_item(key)?;
                ir::Ty::NamedType(item)
            }
            ast::Ty::GenericType(item, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir);

                let key = MonomorphizeKey(item, args);
                let item = self.monomorphize_item(key)?;

                ir::Ty::NamedType(item)
            }
        };

        Ok(self.mono_ctx.ir.intern_type(result))
    }

    fn get_struct_field_map(
        &mut self,
        item: ir::IRItemP<'ir>,
    ) -> HashMap<&'ast str, &'ir ir::Field<'ir>> {
        let MonomorphizeKey(ast_item, _) = self.mono_ctx.reverse_lookup(item);
        let ir_struct = item.get_struct();
        let ast_struct = ast_item.get_struct();

        ast_struct
            .fields
            .iter()
            .map(|ast_f| {
                ir_struct
                    .fields
                    .iter()
                    .find(|ir_f| self.mono_ctx.map_id(ast_f.id) == ir_f.id)
                    .map(|f| (ast_f.name, f))
                    .unwrap()
            })
            .collect()
    }

    fn get_associated_fns(
        &mut self,
        item: ir::IRItemP<'ir>,
    ) -> HashMap<&'ast str, ast::ItemP<'ast>> {
        let MonomorphizeKey(ast_item, _) = self.mono_ctx.reverse_lookup(item);
        let ast_struct = ast_item.get();

        match ast_struct {
            ast::Item::Struct(s) => s.associated_fns.iter().map(|f| (f.name, f.item)).collect(),
            ast::Item::Enum(e) => e.associated_fns.iter().map(|f| (f.name, f.item)).collect(),
            _ => panic!("does not have associated fns"),
        }
    }

    fn make_tentative_child<'b>(&'b mut self) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = self.mono_ctx.ir;

        Monomorphizer {
            mono_ctx: self.mono_ctx,
            replacements: self.replacements.clone(),
            local_types: self.local_types.clone(),
            builder: ExpressionBuilder::new(ir),
            return_type: self.return_type,
            loop_contexts: self.loop_contexts.clone(),
        }
    }

    fn try_coerce(
        &mut self,
        lhs_typ: ir::TyP<'ir>,
        rhs: ir::ExprP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if lhs_typ.assignable_from(rhs.ty) {
            return Ok(rhs);
        }

        let lhs_lang = self.mono_ctx.get_lang_type_kind(lhs_typ);
        let rhs_lang = self.mono_ctx.get_lang_type_kind(rhs.ty);

        // &mut [T] -> &[T]
        match (&lhs_lang, rhs_lang) {
            (Some(LangTypeKind::Slice(t1_ptr)), Some(LangTypeKind::Slice(t2_ptr))) => {
                match (t1_ptr, t2_ptr) {
                    (ir::Ty::Pointer(t1, true), ir::Ty::Pointer(t2, _)) if t1 == t2 => {
                        let item = self.monomorphize_lang_item(LangItemKind::SliceCoerce, [*t1])?;

                        let func = self.builder.function(item);
                        return Ok(self.builder.call(func, [rhs].into_iter(), lhs_typ));
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        // &[T; size] -> &[T]
        // &mut [T; size] -> &[T]
        // &mut [T; size] -> &mut [T]
        // This coercion should be a lang function when we support const usize generics
        match (&lhs_lang, rhs.ty) {
            (
                Some(LangTypeKind::Slice(t1_ptr)),
                ir::Ty::Pointer(ir::Ty::Array(t2, size), t2_const),
            ) => match t1_ptr {
                ir::Ty::Pointer(t1, t1_const)
                    if *t1 == *t2 && (*t1_const || (!*t1_const && !t2_const)) =>
                {
                    let size_lit = self
                        .builder
                        .lit(ir::Lit::Int(*size as u128), builtin!(self, USize));

                    let item = self.monomorphize_lang_item(LangItemKind::SliceNew, [*t1_ptr])?;

                    let func = self.builder.function(item);

                    let data = self
                        .builder
                        .r#ref(self.builder.const_index(self.builder.deref(rhs), 0));

                    return Ok(self.builder.call(
                        func,
                        [data, size_lit].into_iter(),
                        item.get_function().return_type,
                    ));
                }
                _ => {}
            },
            _ => {}
        }

        Err(mismatch!(lhs_typ, rhs.ty)).with_no_span()
    }

    fn try_resolve_function(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&[ast::TyP<'ast>]>,
        self_expr: Option<ir::ExprP<'ir>>,
        tentative_args: Option<&[ast::ExprP<'ast>]>,
        return_type_hint: Option<ir::TyP<'ir>>,
        args_hint: Option<&[ir::TyP<'ir>]>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let fun = item.get_function();

        // If the function is not generic, we don't need to infer the args
        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            return self.monomorphize_item(MonomorphizeKey(item, generic_args));
        }

        if fun.placeholders.is_empty() {
            return self.monomorphize_item(MonomorphizeKey(item, &[]));
        }

        // If the function is generic but no args are provided, we can try to infer the args
        // based on the types of the function's parameters and provided arguments in matching
        // positions and the return type with type_hint Since we have not yet monomorphized the
        // arguments, we do so tentatively in a fresh monomorphizer without the type_hint.
        // If the monomorphization of an argument fails for whatever reason, we skip that arg,
        // but do not rethrow the error as the resolution might still succeed.

        let mut infer_pairs = Vec::new();

        let self_slot = match self_expr {
            Some(self_expr) => Some((fun.args[0].typ, self_expr.ty)),
            None => None,
        };

        if let Some(args) = tentative_args {
            let self_count = self_expr.iter().count();

            if fun.args.len() != args.len() + self_count {
                return Err(AluminaErrorKind::ParamCountMismatch(
                    fun.args.len() - self_count,
                    args.len(),
                ))
                .with_no_span();
            }

            let mut child = self.make_tentative_child();
            infer_pairs.extend(
                fun.args
                    .iter()
                    .skip(self_count)
                    .zip(args.iter())
                    .filter_map(|(p, e)| match child.lower_expr(e, None) {
                        Ok(e) => Some((p.typ, e.ty)),
                        Err(e) => {
                            eprintln!("tentative mono err: {}", e);
                            None
                        }
                    }),
            );
        }

        if let Some(args_hint) = args_hint {
            assert!(tentative_args.is_none());
            assert!(self_slot.is_none());

            infer_pairs.extend(
                fun.args
                    .iter()
                    .zip(args_hint.iter())
                    .map(|(p, e)| (p.typ, *e)),
            );
        }

        if let Some(return_type_hint) = return_type_hint {
            infer_pairs.push((fun.return_type, return_type_hint));
        }

        let mut type_inferer = TypeInferer::new(self.mono_ctx, fun.placeholders.into());

        match type_inferer.try_infer(self_slot, infer_pairs) {
            Some(generic_args) => self.monomorphize_item(MonomorphizeKey(
                item,
                generic_args.alloc_on(self.mono_ctx.ir),
            )),
            None => Err(AluminaErrorKind::TypeHintRequired).with_no_span(),
        }
    }

    fn try_resolve_struct(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&[ast::TyP<'ast>]>,
        initializers: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let r#struct = item.get_struct();

        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            return self.monomorphize_item(MonomorphizeKey(item, generic_args));
        }

        // If the struct is not generic, we don't need to infer the args
        if r#struct.placeholders.is_empty() {
            return self.monomorphize_item(MonomorphizeKey(item, &[]));
        }

        // If the parent of this expression expects a specific struct, we trust that this is
        // in fact the correct monomorphization.
        if let Some(ir::Ty::NamedType(hint_item)) = type_hint {
            let MonomorphizeKey(ast_hint_item, _) = self.mono_ctx.reverse_lookup(hint_item);
            if item == ast_hint_item {
                return Ok(hint_item);
            }
        }

        // See notes in try_resolve_function. Same thing, but for struct fields (we match by name instead of position).

        let mut child = self.make_tentative_child();
        let pairs: Vec<_> = r#struct
            .fields
            .iter()
            .filter_map(|f| {
                initializers
                    .iter()
                    .find(|i| i.name == f.name)
                    .map(|i| (f, i))
            })
            .filter_map(|(p, e)| match child.lower_expr(e.value, None) {
                Ok(e) => Some((p.typ, e.ty)),
                Err(_) => None,
            })
            .collect();

        let mut type_inferer = TypeInferer::new(self.mono_ctx, r#struct.placeholders.into());
        let infer_result = type_inferer.try_infer(None, pairs);

        match infer_result {
            Some(generic_args) => self.monomorphize_item(MonomorphizeKey(
                item,
                generic_args.alloc_on(self.mono_ctx.ir),
            )),
            None => Err(AluminaErrorKind::TypeHintRequired).with_no_span(),
        }
    }

    fn autoref(
        &mut self,
        expr: ir::ExprP<'ir>,
        target: ir::TyP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let mut a: isize = 0;
        let mut a_typ = expr.ty;
        while let ir::Ty::Pointer(inner, _) = a_typ {
            a += 1;
            a_typ = inner;
        }

        let mut b: isize = 0;
        let mut b_typ = target;
        while let ir::Ty::Pointer(inner, _) = b_typ {
            b += 1;
            b_typ = *inner;
        }

        match a - b {
            0 => Ok(expr),
            -1 if matches!(expr.value_type, ValueType::LValue) => Ok(self.builder.r#ref(expr)),
            n if n > 0 => {
                let mut expr = expr;
                for _ in 0..n {
                    expr = self.builder.deref(expr);
                }
                Ok(expr)
            }
            _ => Err(AluminaErrorKind::CannotAddressRValue).with_no_span(),
        }
    }

    fn typecheck_binary(
        &mut self,
        op: ast::BinOp,
        lhs: ir::ExprP<'ir>,
        rhs: ir::ExprP<'ir>,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let result_typ = match (lhs.ty, op, rhs.ty) {
            // Integer builtin types
            (
                Builtin(l),
                BitAnd | BitAnd | BitOr | BitXor | Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus
                | Mul | Div | Mod,
                Builtin(r),
            ) if l == r && l.is_integer() => {
                if op.is_comparison() {
                    Builtin(BuiltinType::Bool)
                } else {
                    *lhs.ty
                }
            }

            (NamedType(l), Eq | Neq, NamedType(r))
                if l == r && matches!(l.get(), ir::IRItem::Enum(_)) =>
            {
                Builtin(BuiltinType::Bool)
            }

            (Builtin(l), LShift | RShift, Builtin(BuiltinType::USize)) if l.is_integer() => *lhs.ty,

            // Float builting types
            (Builtin(l), Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus | Mul | Div, Builtin(r))
                if l == r && l.is_float() =>
            {
                if op.is_comparison() {
                    Builtin(BuiltinType::Bool)
                } else {
                    *lhs.ty
                }
            }

            // Logical operators
            (
                Builtin(BuiltinType::Bool),
                And | Or | BitXor | Eq | Neq,
                Builtin(BuiltinType::Bool),
            ) => Builtin(BuiltinType::Bool),

            // Pointer comparison and pointer difference
            (Pointer(l, _), Eq | Neq | Lt | LEq | Gt | GEq, Pointer(r, _)) if l == r => {
                Builtin(BuiltinType::Bool)
            }

            (Pointer(l, l_const), Minus, Pointer(r, r_const)) if l == r && l_const == r_const => {
                Builtin(BuiltinType::ISize)
            }

            // Pointer arithmetic
            (Pointer(_l, _), Plus | Minus, Builtin(BuiltinType::ISize | BuiltinType::USize)) => {
                *lhs.ty
            }

            _ => return Err(AluminaErrorKind::InvalidBinOp(op)).with_no_span(),
        };

        Ok(self.mono_ctx.ir.intern_type(result_typ))
    }

    fn lower_stmt(
        &mut self,
        stmt: &ast::Statement<'ast>,
    ) -> Result<Vec<ir::Statement<'ir>>, AluminaError> {
        let result = match &stmt.kind {
            ast::StatementKind::Expression(expr) => {
                let expr = self.lower_expr(expr, None)?;
                vec![ir::Statement::Expression(expr)]
            }
            ast::StatementKind::LetDeclaration(decl) => {
                let id = self.mono_ctx.map_id(decl.id);
                let type_hint = decl.typ.map(|t| self.lower_type(t)).transpose()?;
                let init = decl
                    .value
                    .map(|v| self.lower_expr(v, type_hint))
                    .transpose()?;
                match (type_hint, init) {
                    (None, None) => {
                        return Err(AluminaErrorKind::TypeHintRequired).with_span(stmt.span)
                    }
                    (Some(ty), None) => {
                        self.local_types.insert(id, ty);
                        vec![ir::Statement::LocalDef(id, ty)]
                    }
                    (None, Some(init)) => {
                        self.local_types.insert(id, init.ty);

                        vec![
                            ir::Statement::LocalDef(id, init.ty),
                            ir::Statement::Expression(
                                self.builder.assign(self.builder.local(id, init.ty), init),
                            ),
                        ]
                    }
                    (Some(ty), Some(init)) => {
                        let init = self.try_coerce(ty, init)?;

                        self.local_types.insert(id, ty);

                        vec![
                            ir::Statement::LocalDef(id, ty),
                            ir::Statement::Expression(
                                self.builder.assign(self.builder.local(id, ty), init),
                            ),
                        ]
                    }
                }
            }
        };

        Ok(result)
    }

    fn lower_block(
        &mut self,
        statements: &'ast [ast::Statement<'ast>],
        ret: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let statements = statements
            .iter()
            .map(|stmt| self.lower_stmt(stmt))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let ret = self.lower_expr(ret, type_hint)?;

        Ok(self.builder.block(statements, ret))
    }

    fn lower_lit(
        &mut self,
        ret: &ast::Lit<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let (lit, ty) = match ret {
            ast::Lit::Bool(v) => (ir::Lit::Bool(*v), ir::Ty::Builtin(ast::BuiltinType::Bool)),
            ast::Lit::Null => {
                let ty = match type_hint {
                    Some(ir::Ty::Pointer(inner, is_const)) => ir::Ty::Pointer(inner, *is_const),
                    _ => ir::Ty::Pointer(builtin!(self, Void), true),
                };

                (ir::Lit::Null, ty)
            }
            ast::Lit::Int(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => ir::Ty::Builtin(*t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_integer() => ir::Ty::Builtin(*k),
                    _ => ir::Ty::Builtin(BuiltinType::I32),
                };

                (ir::Lit::Int(*v), ty)
            }
            ast::Lit::Float(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => ir::Ty::Builtin(*t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_float() => ir::Ty::Builtin(*k),
                    _ => ir::Ty::Builtin(BuiltinType::I32),
                };

                (ir::Lit::Float(v.alloc_on(self.mono_ctx.ir)), ty)
            }
            ast::Lit::Str(v) => {
                let ptr_type = self
                    .mono_ctx
                    .ir
                    .intern_type(ir::Ty::Pointer(builtin!(self, U8), true));

                let data_lit = self.builder.lit(
                    ir::Lit::Str(self.mono_ctx.ir.arena.alloc_slice_copy(v)),
                    ptr_type,
                );

                let size_lit = self
                    .builder
                    .lit(ir::Lit::Int(v.len() as u128), builtin!(self, USize));

                let item = self.monomorphize_lang_item(LangItemKind::SliceNew, [ptr_type])?;
                let func = self.builder.function(item);
                return Ok(self.builder.call(
                    func,
                    [data_lit, size_lit].into_iter(),
                    item.get_function().return_type,
                ));
            }
        };

        Ok(
            ir::Expr::rvalue(ir::ExprKind::Lit(lit), self.mono_ctx.ir.intern_type(ty))
                .alloc_on(self.mono_ctx.ir),
        )
    }

    fn lower_deref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let span = inner.span;
        let inner = self.lower_expr(
            inner,
            type_hint.map(|ty| self.mono_ctx.ir.intern_type(ir::Ty::Pointer(ty, true))),
        )?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.ty {
            ir::Ty::Pointer(_, _) => self.builder.deref(inner),
            _ => return Err(mismatch!("pointer", inner.ty)).with_no_span(),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_ref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let type_hint = match type_hint {
            Some(ir::Ty::Pointer(inner, _)) => Some(*inner),
            _ => None,
        };

        let inner = self.lower_expr(inner, type_hint)?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.value_type {
            ir::ValueType::LValue => self.builder.r#ref(inner),
            _ => return Err(AluminaErrorKind::CannotAddressRValue).with_no_span(),
        };

        Ok(result)
    }

    fn lower_local(
        &mut self,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let id = self.mono_ctx.map_id(id);
        let typ = self
            .local_types
            .get(&id)
            .copied()
            .expect("local with unknown type");

        Ok(self.builder.local(id, typ))
    }

    fn lower_unary(
        &mut self,
        op: ast::UnOp,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(inner, type_hint)?;
        if inner.diverges() {
            return Ok(inner);
        }

        match (op, inner.ty) {
            (ast::UnOp::Not, ir::Ty::Builtin(BuiltinType::Bool)) => {}
            (ast::UnOp::BitNot, ir::Ty::Builtin(b)) if b.is_integer() => {}
            (ast::UnOp::Neg, ir::Ty::Builtin(b))
                if (b.is_integer() && b.is_signed()) || b.is_float() => {}
            _ => return Err(AluminaErrorKind::InvalidUnOp(op)).with_no_span(),
        };

        let result = ir::Expr::rvalue(ir::ExprKind::Unary(op, inner), inner.ty);

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_binary(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::ExprP<'ast>,
        rhs: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let lhs = self.lower_expr(
            lhs,
            match op {
                Eq | Neq | GEq | LEq | Lt | Gt => None,
                And | Or => Some(builtin!(self, Bool)),
                _ => type_hint,
            },
        )?;

        let rhs = self.lower_expr(
            rhs,
            match op {
                Plus | Minus => match lhs.ty {
                    Pointer(_, _) => Some(builtin!(self, ISize)),
                    _ => Some(lhs.ty),
                },
                LShift | RShift => Some(builtin!(self, USize)),
                _ => Some(lhs.ty),
            },
        )?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

        let result_typ = self.typecheck_binary(op, lhs, rhs)?;

        Ok(self.builder.binary(op, lhs, rhs, result_typ))
    }

    fn lower_assign_op(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::ExprP<'ast>,
        rhs: &ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let lhs = self.lower_expr(lhs, None)?;
        let rhs = self.lower_expr(
            rhs,
            match op {
                Plus | Minus => match lhs.ty {
                    Pointer(_, _) => Some(builtin!(self, ISize)),
                    _ => Some(lhs.ty),
                },
                LShift | RShift => Some(builtin!(self, USize)),
                _ => Some(lhs.ty),
            },
        )?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(AluminaErrorKind::CannotAssignToRValue).with_no_span();
        }

        if lhs.is_const {
            return Err(AluminaErrorKind::CannotAssignToConst).with_no_span();
        }

        let rhs = self.try_coerce(lhs.ty, rhs)?;

        self.typecheck_binary(op, lhs, rhs)?;

        Ok(self.builder.assign_op(op, lhs, rhs))
    }

    fn lower_assign(
        &mut self,
        inner: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let lhs = self.lower_expr(inner, None)?;
        let rhs = self.lower_expr(rhs, Some(lhs.ty))?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(AluminaErrorKind::CannotAssignToRValue).with_no_span();
        }

        if lhs.is_const {
            return Err(AluminaErrorKind::CannotAssignToConst).with_no_span();
        }

        let rhs = self.try_coerce(lhs.ty, rhs)?;

        Ok(self.builder.assign(lhs, rhs))
    }

    fn lower_if(
        &mut self,
        cond: ast::ExprP<'ast>,
        then: ast::ExprP<'ast>,
        els: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let cond = self.lower_expr(cond, Some(builtin!(self, Bool)))?;
        let then = self.lower_expr(then, type_hint)?;
        let els = self.lower_expr(els, Some(then.ty))?;

        if cond.diverges() {
            return Ok(cond);
        }

        let cond = self.try_coerce(builtin!(self, Bool), cond)?;

        let gcd = ir::Ty::gcd(then.ty, els.ty);
        if !gcd.assignable_from(then.ty) || !gcd.assignable_from(els.ty) {
            return Err(AluminaErrorKind::MismatchedBranchTypes(
                format!("{:?}", then.ty),
                format!("{:?}", els.ty),
            ))
            .with_no_span();
        }

        let result = ir::Expr::rvalue(
            ir::ExprKind::If(cond, then, els),
            self.mono_ctx.ir.intern_type(gcd),
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_tuple(
        &mut self,
        exprs: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let type_hints: Vec<_> = match type_hint {
            Some(ir::Ty::Tuple(elems)) if elems.len() == exprs.len() => {
                elems.iter().map(|t| Some(*t)).collect()
            }
            _ => repeat(None).take(exprs.len()).collect(),
        };

        let lowered = exprs
            .iter()
            .zip(type_hints.into_iter())
            .map(|(expr, hint)| self.lower_expr(expr, hint))
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(lowered));
        }

        let element_types: Vec<_> = lowered.iter().map(|e| e.ty).collect();
        let tuple_type = self
            .mono_ctx
            .ir
            .intern_type(ir::Ty::Tuple(element_types.alloc_on(self.mono_ctx.ir)));

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.builder.local(temporary, tuple_type);

        let statements = once(ir::Statement::LocalDef(temporary, tuple_type))
            .chain(lowered.into_iter().enumerate().map(|(i, e)| {
                ir::Statement::Expression(
                    self.builder
                        .assign(self.builder.tuple_index(local, i, e.ty), e),
                )
            }))
            .collect::<Vec<_>>();

        Ok(self.builder.block(statements, local))
    }

    fn lower_cast(
        &mut self,
        expr: ast::ExprP<'ast>,
        target_type: ast::TyP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let expr = self.lower_expr(expr, None)?;
        if expr.diverges() {
            return Ok(expr);
        }

        let typ = self.lower_type(target_type)?;

        // If the type coerces automatically, no cast is required
        if let Some(expr) = self.try_coerce(typ, expr).ok() {
            return Ok(expr);
        }

        match (expr.ty, typ) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}

            // Enums
            (ir::Ty::NamedType(a), ir::Ty::Builtin(b))
                if matches!(a.get(), ir::IRItem::Enum(_)) && b.is_numeric() => {}

            // Pointer casts
            (ir::Ty::Pointer(_, _), ir::Ty::Pointer(_, _)) => {
                // Yes, even const -> mut casts, if you do this you are on your own
            }
            (ir::Ty::Builtin(BuiltinType::USize), ir::Ty::Pointer(_, _)) => {}
            (ir::Ty::Pointer(_, _), ir::Ty::Builtin(BuiltinType::USize)) => {}

            _ => return Err(AluminaErrorKind::InvalidCast).with_no_span(),
        }

        Ok(self.builder.cast(expr, typ))
    }

    fn lower_loop(
        &mut self,
        body: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_result = self.mono_ctx.ir.make_id();
        let break_label = self.mono_ctx.ir.make_id();
        let continue_label = self.mono_ctx.ir.make_id();

        self.loop_contexts.push(LoopContext {
            loop_result,
            type_hint,
            break_label,
            continue_label,
        });

        let body = self.lower_expr(body, None);
        self.loop_contexts.pop();

        let body = body?;
        if body.diverges() {
            return Ok(body);
        }

        let mut statements = vec![
            ir::Statement::Label(continue_label),
            ir::Statement::Expression(body),
            ir::Statement::Expression(self.builder.goto(continue_label)),
            ir::Statement::Label(break_label),
        ];

        let result = match self.local_types.get(&loop_result) {
            None => self.builder.block(statements, self.builder.unreachable()),
            Some(typ) => {
                statements.insert(0, ir::Statement::LocalDef(loop_result, *typ));
                self.builder
                    .block(statements, self.builder.local(loop_result, *typ))
            }
        };

        Ok(result)
    }

    fn lower_break(
        &mut self,
        expr: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self
            .loop_contexts
            .last()
            .expect("break outside of loop")
            .clone();

        let expr = expr
            .map(|e| self.lower_expr(e, loop_context.type_hint))
            .transpose()?;

        if expr.map(|e| e.diverges()).unwrap_or(false) {
            return Ok(expr.unwrap());
        }

        let break_typ = expr.map(|e| e.ty).unwrap_or(builtin!(self, Void));
        let slot_type = match self.local_types.entry(loop_context.loop_result) {
            Entry::Vacant(v) => {
                v.insert(break_typ);
                break_typ
            }
            Entry::Occupied(o) => o.get(),
        };

        let expr = expr
            .map(|expr| self.try_coerce(slot_type, expr))
            .transpose()?
            .unwrap_or(self.builder.void());

        let statements = [ir::Statement::Expression(self.builder.assign(
            self.builder.local(loop_context.loop_result, slot_type),
            expr,
        ))];

        Ok(self
            .builder
            .block(statements, self.builder.goto(loop_context.break_label)))
    }

    fn lower_continue(
        &mut self,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self.loop_contexts.last().expect("continue outside of loop");

        Ok(self.builder.goto(loop_context.continue_label))
    }

    fn lower_method_call(
        &mut self,
        self_arg: ast::ExprP<'ast>,
        unified_fn: Option<ast::ItemP<'ast>>,
        name: &'ast str,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<Option<ir::ExprP<'ir>>, AluminaError> {
        let ir_self_arg = self.lower_expr(self_arg, None)?;

        let method = match ir_self_arg.ty.canonical_type() {
            ir::Ty::NamedType(item) => {
                let fields = self.get_struct_field_map(item);
                if fields.contains_key(name) {
                    // This is not a method, but a field (e.g. a function pointer), go back to lower_call
                    // and process it as usual.
                    return Ok(None);
                }
                self.get_associated_fns(item).get(name).copied()
            }
            _ => None,
        };

        let method = method
            .or(unified_fn)
            .ok_or_else(|| AluminaErrorKind::MethodNotFound(name.into()))
            .with_no_span()?;

        let method = self.try_resolve_function(
            method,
            None,
            Some(ir_self_arg),
            Some(args),
            type_hint,
            None,
        )?;

        let callee = self.builder.function(method);

        let (arg_types, return_type) = match callee.ty {
            ir::Ty::Fn(arg_types, return_type) => (arg_types, return_type),
            _ => unreachable!(),
        };

        if arg_types.is_empty() {
            return Err(AluminaErrorKind::NotAMethod).with_no_span();
        }

        if arg_types.len() != args.len() + 1 {
            return Err(AluminaErrorKind::ParamCountMismatch(
                arg_types.len() - 1,
                args.len(),
            ))
            .with_no_span();
        }

        let ir_self_arg = self
            .autoref(ir_self_arg, arg_types[0])
            .add_span(self_arg.span)?;
        let mut args = once(Ok(ir_self_arg))
            .chain(
                args.iter()
                    .zip(arg_types.iter().skip(1))
                    .map(|(arg, ty)| self.lower_expr(arg, Some(ty))),
            )
            .collect::<Result<Vec<_>, _>>()?;

        if args.iter().any(|e| e.diverges()) {
            return Ok(Some(self.builder.diverges(args)));
        }

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, *arg)?;
        }

        let result = ir::Expr::rvalue(
            ir::ExprKind::Call(callee, args.alloc_on(self.mono_ctx.ir)),
            return_type,
        );

        Ok(Some(result.alloc_on(self.mono_ctx.ir)))
    }

    fn lower_call(
        &mut self,
        callee: ast::ExprP<'ast>,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // Function calls are not completely referentially tranparent, as we do not support
        // pointers-to-method, so these need to be invoked directly. This allow us to switch on the
        // callee's expression kind to determine how to handle it.

        let callee = match &callee.kind {
            ast::ExprKind::Fn(ast::FnKind::Normal(item), generic_args) => {
                let item = self.try_resolve_function(
                    item,
                    *generic_args,
                    None,
                    Some(args),
                    type_hint,
                    None,
                )?;

                self.builder.function(item)
            }
            ast::ExprKind::Fn(ast::FnKind::Defered(spec), generic_args) => {
                let typ = match self.replacements.get(&spec.placeholder) {
                    Some(ir::Ty::NamedType(typ)) => typ,
                    _ => unreachable!(),
                };

                let associated_fns = self.get_associated_fns(typ);
                let func = associated_fns
                    .get(spec.name)
                    .ok_or(AluminaErrorKind::UnresolvedItem(spec.name.to_string()))
                    .with_no_span()?;

                let item = self.try_resolve_function(
                    func,
                    *generic_args,
                    None,
                    Some(args),
                    type_hint,
                    None,
                )?;

                self.builder.function(item)
            }
            ast::ExprKind::Field(e, field, unified_fn) => {
                // Methods are resolved in the following order - field has precedence, then associated
                // functions, then free functions with UFCS. We never want UFCS to shadow native fields.
                match self.lower_method_call(e, *unified_fn, field, args, type_hint)? {
                    Some(result) => return Ok(result),
                    None => self.lower_expr(callee, None)?,
                }
            }
            _ => self.lower_expr(callee, None)?,
        };

        let (arg_types, return_type) = match callee.ty {
            ir::Ty::Fn(arg_types, return_type) => (arg_types, return_type),
            _ => return Err(AluminaErrorKind::FunctionExpectedHere).with_no_span(),
        };

        if arg_types.len() != args.len() {
            return Err(AluminaErrorKind::ParamCountMismatch(
                arg_types.len(),
                args.len(),
            ))
            .with_no_span();
        }

        let mut args = args
            .iter()
            .zip(arg_types.iter())
            .map(|(arg, ty)| self.lower_expr(arg, Some(ty)))
            .collect::<Result<Vec<_>, _>>()?;

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, *arg)?;
        }

        if callee.diverges() || args.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(once(callee).chain(args)));
        }

        let result = ir::Expr::rvalue(
            ir::ExprKind::Call(callee, args.alloc_on(self.mono_ctx.ir)),
            return_type,
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_fn(
        &mut self,
        kind: ast::FnKind<'ast>,
        generic_args: Option<&'ast [ast::TyP<'ast>]>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // TODO: Forward the type hint inside the function body.

        let (args_hint, return_type_hint) = match type_hint {
            Some(ir::Ty::Fn(args, ret)) => (Some(*args), Some(*ret)),
            _ => (None, None),
        };

        let result = match kind {
            ast::FnKind::Normal(item) => {
                let item = self.try_resolve_function(
                    item,
                    generic_args,
                    None,
                    None,
                    return_type_hint,
                    args_hint,
                )?;

                self.builder.function(item)
            }
            ast::FnKind::Defered(spec) => {
                let typ = match self.replacements.get(&spec.placeholder) {
                    Some(ir::Ty::NamedType(typ)) => typ,
                    _ => unreachable!(),
                };

                let associated_fns = self.get_associated_fns(typ);
                let func = associated_fns
                    .get(spec.name)
                    .ok_or(AluminaErrorKind::UnresolvedItem(spec.name.to_string()))
                    .with_no_span()?;

                let item = self.try_resolve_function(
                    func,
                    generic_args,
                    None,
                    None,
                    return_type_hint,
                    args_hint,
                )?;

                self.builder.function(item)
            }
        };

        Ok(result)
    }

    fn lower_tuple_index(
        &mut self,
        tup: ast::ExprP<'ast>,
        index: usize,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let span = tup.span;
        let tup = self.lower_expr(tup, None)?;
        let result = match tup.ty {
            ir::Ty::Tuple(types) => {
                if types.len() <= index {
                    return Err(AluminaErrorKind::TupleIndexOutOfBounds).with_no_span();
                }
                self.builder.tuple_index(tup, index, types[index])
            }
            _ => return Err(mismatch!("tuple", tup.ty)).with_span(span),
        };

        // We want to typecheck even if it diverges, no point in trying to access
        // tuple fields of non-tuples.
        if tup.diverges() {
            return Ok(tup);
        }

        Ok(result)
    }

    fn lower_field(
        &mut self,
        obj: ast::ExprP<'ast>,
        field: &'ast str,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let obj_span = obj.span;
        let obj = self.lower_expr(obj, None)?;

        let result = match obj.ty.canonical_type() {
            ir::Ty::NamedType(item) => {
                let field_map = self.get_struct_field_map(item);
                let field = field_map
                    .get(field)
                    .ok_or(AluminaErrorKind::UnresolvedItem(field.to_string()))
                    .with_no_span()?;

                let mut obj = obj;
                while let ir::Ty::Pointer(_, _) = obj.ty {
                    obj = self.builder.deref(obj);
                }

                self.builder.field(obj, field.id, field.ty)
            }
            _ => return Err(AluminaErrorKind::StructExpectedHere).with_span(obj_span),
        };

        Ok(result)
    }

    fn lower_index(
        &mut self,
        inner: ast::ExprP<'ast>,
        index: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner_span = inner.span;
        let inner = self.lower_expr(
            inner,
            type_hint.map(|ty| self.mono_ctx.ir.intern_type(ir::Ty::Pointer(ty, true))),
        )?;

        let index = self.lower_expr(index, Some(builtin!(self, USize)))?;

        if inner.diverges() || index.diverges() {
            return Ok(self.builder.diverges([inner, index]));
        }

        let index = self.try_coerce(builtin!(self, USize), index)?;

        let result = match inner.ty {
            ir::Ty::Array(_, _) | ir::Ty::Pointer(_, _) => self.builder.index(inner, index),
            _ => {
                let inner_lang = self.mono_ctx.get_lang_type_kind(inner.ty);

                match inner_lang {
                    Some(LangTypeKind::Slice(ptr_ty)) => {
                        let item =
                            self.monomorphize_lang_item(LangItemKind::SliceIndex, [ptr_ty])?;
                        let func = self.builder.function(item);
                        return Ok(self.builder.deref(self.builder.call(
                            func,
                            [inner, index].into_iter(),
                            ptr_ty,
                        )));
                    }
                    _ => {}
                }

                return Err(mismatch!("array or pointer", inner.ty)).with_span(inner_span);
            }
        };

        Ok(result)
    }

    fn lower_range_index(
        &mut self,
        inner: ast::ExprP<'ast>,
        lower: Option<ast::ExprP<'ast>>,
        upper: Option<ast::ExprP<'ast>>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(
            inner,
            // slice slices to another slice. It could also be an array, but wcyd
            type_hint,
        )?;

        let lower = lower
            .map(|e| self.lower_expr(e, Some(builtin!(self, USize))))
            .transpose()?;

        let upper = upper
            .map(|e| self.lower_expr(e, Some(builtin!(self, USize))))
            .transpose()?;

        let stack = [Some(inner), lower, upper]
            .into_iter()
            .filter_map(|e| e)
            .collect::<Vec<_>>();

        if stack.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(stack));
        }

        let inner_lang = self.mono_ctx.get_lang_type_kind(inner.ty);
        let result = match inner_lang {
            Some(LangTypeKind::Slice(ptr_ty)) => {
                let lower = lower
                    .unwrap_or_else(|| self.builder.lit(Lit::Int(0u128), builtin!(self, USize)));
                match upper {
                    Some(upper) => {
                        let item =
                            self.monomorphize_lang_item(LangItemKind::SliceRangeIndex, [ptr_ty])?;
                        let func = self.builder.function(item);
                        self.builder
                            .call(func, [inner, lower, upper].into_iter(), inner.ty)
                    }
                    None => {
                        let item = self
                            .monomorphize_lang_item(LangItemKind::SliceRangeIndexLower, [ptr_ty])?;
                        let func = self.builder.function(item);
                        self.builder
                            .call(func, [inner, lower].into_iter(), inner.ty)
                    }
                }
            }
            _ => return Err(AluminaErrorKind::RangeIndexNonSlice).with_no_span(),
        };

        Ok(result)
    }

    fn lower_return(
        &mut self,
        inner: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = inner
            .map(|inner| self.lower_expr(inner, self.return_type))
            .transpose()?
            .unwrap_or_else(|| self.builder.void());

        if inner.diverges() {
            return Ok(inner);
        }

        let inner = self.try_coerce(self.return_type.unwrap(), inner)?;

        Ok(self.builder.ret(inner))
    }

    fn lower_struct_expression(
        &mut self,
        typ: ast::TyP<'ast>,
        inits: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item = match typ {
            ast::Ty::NamedType(item) => self.try_resolve_struct(item, None, inits, type_hint)?,
            ast::Ty::GenericType(item, generic_args) => {
                self.try_resolve_struct(item, Some(generic_args), inits, type_hint)?
            }
            _ => return Err(AluminaErrorKind::StructExpectedHere).with_no_span(),
        };

        let field_map = self.get_struct_field_map(item);
        let lowered = inits
            .iter()
            .map(|f| match field_map.get(&f.name) {
                Some(field) => self
                    .lower_expr(f.value, Some(field.ty))
                    .and_then(|e| self.try_coerce(field.ty, e))
                    .map(|i| (*field, i)),
                None => Err(AluminaErrorKind::UnresolvedItem(f.name.to_string())).with_span(f.span),
            })
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|(_, e)| e.diverges()) {
            return Ok(self.builder.diverges(lowered.into_iter().map(|(_, e)| e)));
        }

        let struct_type = self.mono_ctx.ir.intern_type(ir::Ty::NamedType(item));

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.builder.local(temporary, struct_type);

        let statements = once(ir::Statement::LocalDef(temporary, struct_type))
            .chain(lowered.into_iter().map(|(f, e)| {
                ir::Statement::Expression(
                    self.builder
                        .assign(self.builder.field(local, f.id, f.ty), e),
                )
            }))
            .collect::<Vec<_>>();

        Ok(self.builder.block(statements, local))
    }

    fn lower_array_expression(
        &mut self,
        elements: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let element_type_hint = match type_hint {
            Some(ir::Ty::Array(item, _)) => Some(*item),
            _ => None,
        };

        let mut first_elem_type = None;
        let lowered = elements
            .iter()
            .map(|expr| {
                self.lower_expr(expr, first_elem_type.or(element_type_hint))
                    .and_then(|e| self.try_coerce(first_elem_type.get_or_insert(e.ty), e))
            })
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(lowered.into_iter()));
        }

        let element_type = first_elem_type.or(element_type_hint);
        let array_type = match element_type {
            Some(element_type) => self
                .mono_ctx
                .ir
                .intern_type(ir::Ty::Array(element_type, elements.len())),
            None => return Err(AluminaErrorKind::TypeHintRequired).with_no_span(),
        };

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.builder.local(temporary, array_type);

        let statements = once(ir::Statement::LocalDef(temporary, array_type))
            .chain(lowered.into_iter().enumerate().map(|(idx, e)| {
                ir::Statement::Expression(
                    self.builder.assign(self.builder.const_index(local, idx), e),
                )
            }))
            .collect::<Vec<_>>();

        Ok(self.builder.block(statements, local))
    }

    fn lower_enum_value(
        &mut self,
        typ: ast::ItemP<'ast>,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.monomorphize(typ)?;
        let ir_id = self.mono_ctx.map_id(id);
        let result = match item_cell.try_get() {
            Some(ir::IRItem::Enum(item)) => {
                let typ = self.mono_ctx.ir.intern_type(ir::Ty::NamedType(item_cell));
                ir::Expr::rvalue(
                    ir::ExprKind::Cast(item.members.iter().find(|v| v.id == ir_id).unwrap().value),
                    typ,
                )
            }
            _ => return Err(AluminaErrorKind::CycleDetected).with_no_span(),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_expr(
        &mut self,
        expr: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let result = match &expr.kind {
            ast::ExprKind::Void => Ok(self.builder.void()),
            ast::ExprKind::Block(statements, ret) => self.lower_block(statements, ret, type_hint),
            ast::ExprKind::Lit(lit) => self.lower_lit(lit, type_hint),
            ast::ExprKind::Deref(expr) => self.lower_deref(expr, type_hint),
            ast::ExprKind::Ref(expr) => self.lower_ref(expr, type_hint),
            ast::ExprKind::Local(id) => self.lower_local(*id, type_hint),
            ast::ExprKind::Unary(op, inner) => self.lower_unary(*op, inner, type_hint),
            ast::ExprKind::Assign(lhs, rhs) => self.lower_assign(lhs, rhs, type_hint),
            ast::ExprKind::If(cond, then, els) => self.lower_if(cond, then, els, type_hint),
            ast::ExprKind::Cast(expr, typ) => self.lower_cast(expr, typ, type_hint),
            ast::ExprKind::Loop(body) => self.lower_loop(body, type_hint),
            ast::ExprKind::Binary(op, lhs, rhs) => self.lower_binary(*op, lhs, rhs, type_hint),
            ast::ExprKind::AssignOp(op, lhs, rhs) => self.lower_assign_op(*op, lhs, rhs, type_hint),
            ast::ExprKind::Break(value) => self.lower_break(*value, type_hint),
            ast::ExprKind::Continue => self.lower_continue(type_hint),
            ast::ExprKind::Tuple(exprs) => self.lower_tuple(exprs, type_hint),
            ast::ExprKind::TupleIndex(tup, index) => self.lower_tuple_index(tup, *index, type_hint),
            ast::ExprKind::Field(tup, field, _) => self.lower_field(tup, field, type_hint),
            ast::ExprKind::Call(func, args) => self.lower_call(func, args, type_hint),
            ast::ExprKind::Array(elements) => self.lower_array_expression(elements, type_hint),
            ast::ExprKind::EnumValue(typ, id) => self.lower_enum_value(typ, *id, type_hint),
            ast::ExprKind::Struct(func, initializers) => {
                self.lower_struct_expression(func, initializers, type_hint)
            }
            ast::ExprKind::Index(inner, index) => self.lower_index(inner, index, type_hint),
            ast::ExprKind::RangeIndex(inner, lower, upper) => {
                self.lower_range_index(inner, *lower, *upper, type_hint)
            }
            ast::ExprKind::Return(inner) => self.lower_return(*inner, type_hint),
            ast::ExprKind::Fn(item, args) => self.lower_fn(item.clone(), *args, type_hint),
            _ => panic!("unimplemented {:?}", expr),
        };
        /*
                let result = match result {
                    Ok(result) => result,
                    Err(e) => {
                        panic!("{:?} at {:?}", e, expr);
                    }
                };
        */
        result.add_span(expr.span)
    }
}
