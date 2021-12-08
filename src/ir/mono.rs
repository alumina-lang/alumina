use core::panic;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;
use std::iter::{once, repeat};

use once_cell::sync::{Lazy, OnceCell};

use super::builder::ExpressionBuilder;
use super::const_eval::{const_eval, numeric_of_kind, Value};
use super::infer::TypeInferer;
use super::optimize::Optimizer;
use super::{Enum, IrCtx};
use crate::ast::{expressions, BuiltinType};
use crate::common::ArenaAllocatable;
use crate::ir::{FuncBodyCell, ValueType};
use crate::{ast, common::AluminaError, ir};

macro_rules! builtin {
    ($self:expr, $name:ident) => {
        $self
            .mono_ctx
            .ir
            .intern_type(crate::ir::Ty::Builtin(crate::ast::BuiltinType::$name))
    };
}

pub struct MonoCtx<'ast, 'ir> {
    ir: &'ir ir::IrCtx<'ir>,
    id_map: HashMap<ast::AstId, ir::IrId>,

    finished: HashMap<MonomorphizeKey<'ast, 'ir>, ir::IRItemP<'ir>>,
    reverse_map: HashMap<ir::IRItemP<'ir>, MonomorphizeKey<'ast, 'ir>>,
}

impl<'ast, 'ir> MonoCtx<'ast, 'ir> {
    pub fn new(ir: &'ir ir::IrCtx<'ir>) -> Self {
        MonoCtx {
            ir,
            id_map: HashMap::new(),
            finished: HashMap::new(),
            reverse_map: HashMap::new(),
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
                    return Err(AluminaError::GenericParamCountMismatch(0, key.1.len()));
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

                    if value_type != *type_hint.get_or_insert(value_type) {
                        return Err(AluminaError::TypeMismatch);
                    }

                    if !taken_values.insert(value) {
                        return Err(AluminaError::DuplicateEnumMember);
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
                    underlying_type: type_hint.unwrap(),
                    members: members.alloc_on(child.mono_ctx.ir),
                });

                item.assign(res);
            }
            ast::Item::Function(func) => {
                if key.1.len() != func.placeholders.len() {
                    return Err(AluminaError::GenericParamCountMismatch(
                        func.placeholders.len(),
                        key.1.len(),
                    ));
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
                    let body = child.lower_expr(
                        body,
                        Some(return_type),
                    )?;

                    if !return_type.assignable_from(body.typ) {
                        return Err(AluminaError::TypeMismatch);
                    }

                    let mut optimizer = Optimizer::new(child.mono_ctx.ir);
                    let optimized = optimizer.optimize_func_body(body);

                    item.get_function().body.assign(optimized);
                }
            }
            ast::Item::Struct(s) => {
                if key.1.len() != s.placeholders.len() {
                    return Err(AluminaError::GenericParamCountMismatch(
                        s.placeholders.len(),
                        key.1.len(),
                    ));
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
                    fields: fields.alloc_on(self.mono_ctx.ir),
                });
                item.assign(res);
            }
        };

        Ok(item)
    }

    pub fn lower_type(&mut self, typ: ast::TyP<'ast>) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *typ {
            // TODO: can coalesce same usize == u64 depending on platform here I guess
            ast::Ty::Builtin(kind) => ir::Ty::Builtin(kind),
            ast::Ty::Array(inner, len) => ir::Ty::Array(self.lower_type(inner)?, len),
            ast::Ty::Pointer(inner, is_const) => ir::Ty::Pointer(self.lower_type(inner)?, is_const),
            ast::Ty::Slice(inner) => ir::Ty::Slice(self.lower_type(inner)?),
            ast::Ty::Extern(id) => ir::Ty::Extern(self.mono_ctx.map_id(id)),
            ast::Ty::Function(args, ret) => ir::Ty::Fn(
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

    fn try_resolve_function(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&[ast::TyP<'ast>]>,
        self_expr: Option<ir::ExprP<'ir>>,
        args: Option<&[ast::ExprP<'ast>]>,
        return_type_hint: Option<ir::TyP<'ir>>,
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
            Some(self_expr) => Some((fun.args[0].typ, self_expr.typ)),
            None => None,
        };

        if let Some(args) = args {
            let self_count = self_expr.iter().count();

            if fun.args.len() != args.len() + self_count {
                return Err(AluminaError::ParamCountMismatch(
                    fun.args.len() - self_count,
                    args.len(),
                ));
            }

            let mut child = self.make_tentative_child();
            infer_pairs.extend(
                fun.args
                    .iter()
                    .skip(self_count)
                    .zip(args.iter())
                    .filter_map(|(p, e)| match child.lower_expr(e, None) {
                        Ok(e) => Some((p.typ, e.typ)),
                        Err(_) => None,
                    }),
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
            None => Err(AluminaError::TypeHintRequired),
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
                Ok(e) => Some((p.typ, e.typ)),
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
            None => Err(AluminaError::TypeHintRequired),
        }
    }

    fn autoref(
        &mut self,
        expr: ir::ExprP<'ir>,
        target: ir::TyP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let mut a: isize = 0;
        let mut a_typ = expr.typ;
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
            _ => Err(AluminaError::CannotAddressRValue),
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

        let result_typ = match (lhs.typ, op, rhs.typ) {
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
                    *lhs.typ
                }
            }

            (NamedType(l), Eq | Neq, NamedType(r))
                if l == r && matches!(l.get(), ir::IRItem::Enum(_)) =>
            {
                Builtin(BuiltinType::Bool)
            }

            (Builtin(l), LShift | RShift, Builtin(BuiltinType::USize)) if l.is_integer() => {
                *lhs.typ
            }

            // Float builting types
            (Builtin(l), Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus | Mul | Div, Builtin(r))
                if l == r && l.is_float() =>
            {
                if op.is_comparison() {
                    Builtin(BuiltinType::Bool)
                } else {
                    *lhs.typ
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
                *lhs.typ
            }

            // Pointer arithmetic
            (Pointer(l, _), Plus | Minus, Builtin(BuiltinType::ISize | BuiltinType::USize)) => {
                *lhs.typ
            }

            _ => return Err(AluminaError::InvalidBinOp(op)),
        };

        Ok(self.mono_ctx.ir.intern_type(result_typ))
    }

    fn lower_stmt(
        &mut self,
        stmt: &ast::Statement<'ast>,
    ) -> Result<Vec<ir::Statement<'ir>>, AluminaError> {
        let result = match stmt {
            ast::Statement::Expression(expr) => {
                let expr = self.lower_expr(expr, None)?;
                vec![ir::Statement::Expression(expr)]
            }
            ast::Statement::LetDeclaration(decl) => {
                let id = self.mono_ctx.map_id(decl.id);
                let type_hint = decl.typ.map(|t| self.lower_type(t)).transpose()?;
                let init = decl
                    .value
                    .map(|v| self.lower_expr(v, type_hint))
                    .transpose()?;
                match (type_hint, init) {
                    (None, None) => return Err(AluminaError::TypeHintRequired),
                    (Some(ty), None) => {
                        self.local_types.insert(id, ty);
                        vec![ir::Statement::LocalDef(id, ty)]
                    }
                    (_, Some(init)) => {
                        match type_hint {
                            Some(ty) if !ty.assignable_from(init.typ) => {
                                return Err(AluminaError::TypeMismatch);
                            }
                            _ => {}
                        };

                        self.local_types.insert(id, init.typ);

                        vec![
                            ir::Statement::LocalDef(id, init.typ),
                            ir::Statement::Expression(
                                self.builder.assign(self.builder.local(id, init.typ), init),
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
            &ast::Lit::Bool(v) => (ir::Lit::Bool(v), ir::Ty::Builtin(ast::BuiltinType::Bool)),
            &ast::Lit::Null => {
                let ty = match type_hint {
                    Some(ir::Ty::Pointer(inner, _)) => ir::Ty::Pointer(inner, true),
                    _ => ir::Ty::Pointer(builtin!(self, Void), true),
                };

                (ir::Lit::Null, ty)
            }
            &ast::Lit::Int(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => ir::Ty::Builtin(t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_integer() => ir::Ty::Builtin(*k),
                    _ => ir::Ty::Builtin(BuiltinType::I32),
                };

                (ir::Lit::Int(v), ty)
            }
            &ast::Lit::Float(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => ir::Ty::Builtin(t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_float() => ir::Ty::Builtin(*k),
                    _ => ir::Ty::Builtin(BuiltinType::I32),
                };

                (ir::Lit::Float(v.alloc_on(self.mono_ctx.ir)), ty)
            }
            _ => unimplemented!(),
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
        let inner = self.lower_expr(
            inner,
            type_hint.map(|ty| self.mono_ctx.ir.intern_type(ir::Ty::Pointer(ty, true))),
        )?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.typ {
            ir::Ty::Pointer(_, _) => self.builder.deref(inner),
            _ => return Err(AluminaError::TypeMismatch),
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
            _ => return Err(AluminaError::CannotAddressRValue),
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

        match (op, inner.typ) {
            (ast::UnOp::Not, ir::Ty::Builtin(BuiltinType::Bool)) => {}
            (ast::UnOp::BitNot, ir::Ty::Builtin(b)) if b.is_integer() => {}
            (ast::UnOp::Neg, ir::Ty::Builtin(b))
                if (b.is_integer() && b.is_signed()) || b.is_float() => {}
            _ => return Err(AluminaError::TypeMismatch),
        };

        let result = ir::Expr::rvalue(ir::ExprKind::Unary(op, inner), inner.typ);

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
                Plus | Minus => match lhs.typ {
                    Pointer(_, _) => Some(builtin!(self, ISize)),
                    _ => Some(lhs.typ),
                },
                LShift | RShift => Some(builtin!(self, USize)),
                _ => Some(lhs.typ),
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
                Plus | Minus => match lhs.typ {
                    Pointer(_, _) => Some(builtin!(self, ISize)),
                    _ => Some(lhs.typ),
                },
                LShift | RShift => Some(builtin!(self, USize)),
                _ => Some(lhs.typ),
            },
        )?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(AluminaError::CannotAssignToRValue);
        }

        if lhs.is_const {
            return Err(AluminaError::CannotAssignToConst);
        }

        if !lhs.typ.assignable_from(rhs.typ) {
            return Err(AluminaError::TypeMismatch);
        }

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
        let rhs = self.lower_expr(rhs, Some(lhs.typ))?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(AluminaError::CannotAssignToRValue);
        }

        if lhs.is_const {
            return Err(AluminaError::CannotAssignToConst);
        }

        if !lhs.typ.assignable_from(rhs.typ) {
            return Err(AluminaError::TypeMismatch);
        }

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
        let els = self.lower_expr(els, Some(then.typ))?;

        if cond.diverges() {
            return Ok(cond);
        }

        if !builtin!(self, Bool).assignable_from(cond.typ) {
            return Err(AluminaError::TypeMismatch);
        }

        eprintln!("{:?}", type_hint);
        eprintln!("{:?}", then.typ);
        eprintln!("{:?}", els.typ);

        let gcd = ir::Ty::gcd(then.typ, els.typ);
        if !gcd.assignable_from(then.typ) || !gcd.assignable_from(els.typ) {
            return Err(AluminaError::TypeMismatch);
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

        let element_types: Vec<_> = lowered.iter().map(|e| e.typ).collect();
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
                        .assign(self.builder.tuple_index(local, i, e.typ), e),
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

        match (expr.typ, typ) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}

            // Pointer casts
            (ir::Ty::Pointer(_, _), ir::Ty::Pointer(_, _)) => {}
            (ir::Ty::Builtin(BuiltinType::USize), ir::Ty::Pointer(_, _)) => {}
            (ir::Ty::Pointer(_, _), ir::Ty::Builtin(BuiltinType::USize)) => {}

            _ => return Err(AluminaError::InvalidCast),
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
            ir::Statement::Goto(continue_label),
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
        type_hint: Option<ir::TyP<'ir>>,
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

        let break_typ = expr.map(|e| e.typ).unwrap_or(builtin!(self, Void));
        let slot_type = match self.local_types.entry(loop_context.loop_result) {
            Entry::Vacant(v) => {
                v.insert(break_typ);
                break_typ
            }
            Entry::Occupied(o) => o.get(),
        };

        if !slot_type.assignable_from(break_typ) {
            return Err(AluminaError::TypeMismatch);
        }

        let statements = [
            ir::Statement::Expression(self.builder.assign(
                self.builder.local(loop_context.loop_result, slot_type),
                expr.unwrap_or(self.builder.void()),
            )),
            ir::Statement::Goto(loop_context.break_label),
        ];

        Ok(self.builder.block(statements, self.builder.unreachable()))
    }

    fn lower_continue(
        &mut self,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self.loop_contexts.last().expect("continue outside of loop");

        let statements = [ir::Statement::Goto(loop_context.continue_label)];

        Ok(self.builder.block(statements, self.builder.unreachable()))
    }

    fn lower_method_call(
        &mut self,
        self_arg: ast::ExprP<'ast>,
        unified_fn: Option<ast::ItemP<'ast>>,
        name: &'ast str,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let ir_self_arg = self.lower_expr(self_arg, None)?;
        let method = match ir_self_arg.typ.canonical_type() {
            ir::Ty::NamedType(item) => self.get_associated_fns(item).get(name).copied(),
            _ => None,
        };

        let method = method
            .or(unified_fn)
            .ok_or_else(|| AluminaError::MethodNotFound(name.into()))?;

        let method =
            self.try_resolve_function(method, None, Some(ir_self_arg), Some(args), type_hint)?;

        let callee = self.builder.function(method);

        let (arg_types, return_type) = match callee.typ {
            ir::Ty::Fn(arg_types, return_type) => (arg_types, return_type),
            _ => unreachable!(),
        };

        if arg_types.is_empty() {
            return Err(AluminaError::NotAMethod);
        }

        if arg_types.len() != args.len() + 1 {
            return Err(AluminaError::ParamCountMismatch(
                arg_types.len() - 1,
                args.len(),
            ));
        }

        let ir_self_arg = self.autoref(ir_self_arg, arg_types[0])?;
        let args = once(Ok(ir_self_arg))
            .chain(
                args.iter()
                    .zip(arg_types.iter().skip(1))
                    .map(|(arg, ty)| self.lower_expr(arg, Some(ty))),
            )
            .collect::<Result<Vec<_>, _>>()?;

        if args.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(args));
        }

        for (expected, arg) in arg_types.iter().zip(args.iter()) {
            if !expected.assignable_from(arg.typ) {
                return Err(AluminaError::TypeMismatch);
            }
        }

        let result = ir::Expr::rvalue(
            ir::ExprKind::Call(callee, args.alloc_on(self.mono_ctx.ir)),
            return_type,
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
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

        let callee = match callee {
            ast::Expr::Fn(ast::FnKind::Normal(item), generic_args) => {
                let item =
                    self.try_resolve_function(item, *generic_args, None, Some(args), type_hint)?;

                self.builder.function(item)
            }
            ast::Expr::Fn(ast::FnKind::Defered(spec), generic_args) => {
                let typ = match self.replacements.get(&spec.placeholder) {
                    Some(ir::Ty::NamedType(typ)) => typ,
                    _ => unreachable!(),
                };

                let associated_fns = self.get_associated_fns(typ);
                let func = associated_fns
                    .get(spec.name)
                    .ok_or(AluminaError::UnresolvedItem(spec.name.to_string()))?;

                let item =
                    self.try_resolve_function(func, *generic_args, None, Some(args), type_hint)?;

                self.builder.function(item)
            }
            ast::Expr::Field(e, field, unified_fn) => {
                return self.lower_method_call(e, *unified_fn, field, args, type_hint);
            }
            _ => unimplemented!(),
        };

        let (arg_types, return_type) = match callee.typ {
            ir::Ty::Fn(arg_types, return_type) => (arg_types, return_type),
            _ => return Err(AluminaError::FunctionExpectedHere),
        };

        if arg_types.len() != args.len() {
            return Err(AluminaError::ParamCountMismatch(
                arg_types.len(),
                args.len(),
            ));
        }

        let args = args
            .iter()
            .zip(arg_types.iter())
            .map(|(arg, ty)| self.lower_expr(arg, Some(ty)))
            .collect::<Result<Vec<_>, _>>()?;

        for (expected, arg) in arg_types.iter().zip(args.iter()) {
            if !expected.assignable_from(arg.typ) {
                return Err(AluminaError::TypeMismatch);
            }
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
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        panic!()
    }

    fn lower_tuple_index(
        &mut self,
        tup: ast::ExprP<'ast>,
        index: usize,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let tup = self.lower_expr(tup, None)?;
        let result = match tup.typ {
            ir::Ty::Tuple(types) => {
                if types.len() <= index {
                    return Err(AluminaError::TupleIndexOutOfBounds);
                }
                self.builder.tuple_index(tup, index, types[index])
            }
            _ => return Err(AluminaError::TypeMismatch),
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
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let obj = self.lower_expr(obj, None)?;

        let result = match obj.typ.canonical_type() {
            ir::Ty::NamedType(item) => {
                let field_map = self.get_struct_field_map(item);
                let field = field_map
                    .get(field)
                    .ok_or(AluminaError::UnresolvedItem(field.to_string()))?;

                let mut obj = obj;
                while let ir::Ty::Pointer(_, _) = obj.typ {
                    obj = self.builder.deref(obj);
                }

                self.builder.field(obj, field.id, field.ty)
            }
            _ => return Err(AluminaError::StructExpectedHere),
        };

        Ok(result)
    }

    fn lower_index(
        &mut self,
        inner: ast::ExprP<'ast>,
        index: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(
            inner,
            type_hint.map(|ty| self.mono_ctx.ir.intern_type(ir::Ty::Pointer(ty, true))),
        )?;

        let index = self.lower_expr(index, Some(builtin!(self, USize)))?;

        if inner.diverges() || index.diverges() {
            return Ok(self.builder.diverges([inner, index]));
        }

        let result = match (inner.typ, index.typ) {
            (ir::Ty::Array(_, _) | ir::Ty::Pointer(_, _), ir::Ty::Builtin(BuiltinType::USize)) => {
                self.builder.index(inner, index)
            }
            _ => return Err(AluminaError::TypeMismatch),
        };

        Ok(result)
    }

    fn lower_return(
        &mut self,
        inner: Option<ast::ExprP<'ast>>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = inner
            .map(|inner| self.lower_expr(inner, self.return_type))
            .transpose()?
            .unwrap_or_else(|| self.builder.void());

        if inner.diverges() {
            return Ok(inner);
        }

        if !self
            .return_type
            .get_or_insert(inner.typ)
            .assignable_from(inner.typ)
        {
            return Err(AluminaError::TypeMismatch);
        }

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
            _ => return Err(AluminaError::StructExpectedHere),
        };

        let field_map = self.get_struct_field_map(item);
        let lowered = inits
            .iter()
            .map(|f| match field_map.get(&f.name) {
                Some(field) => self
                    .lower_expr(f.value, Some(field.ty))
                    .map(|i| (*field, i)),
                None => Err(AluminaError::UnresolvedItem(f.name.to_string())),
            })
            .collect::<Result<Vec<_>, _>>()?;

        for (f, e) in lowered.iter() {
            if !f.ty.assignable_from(e.typ) {
                return Err(AluminaError::TypeMismatch);
            }
        }

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

    fn lower_enum_value(
        &mut self,
        typ: ast::ItemP<'ast>,
        id: ast::AstId,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.monomorphize(typ)?;
        let ir_id = self.mono_ctx.map_id(id);
        let result = match item_cell.try_get() {
            Some(ir::IRItem::Enum(item)) => {
                let typ = self.mono_ctx.ir.intern_type(ir::Ty::NamedType(item_cell));
                ir::Expr::rvalue(
                    ir::ExprKind::Cast(
                        item.members.iter().find(|v| v.id == ir_id).unwrap().value,
                    ),
                    typ,
                )
            }
            _ => return Err(AluminaError::CycleDetected),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_expr(
        &mut self,
        expr: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let result = match expr {
            ast::Expr::Void => Ok(self.builder.void()),
            ast::Expr::Block(statements, ret) => self.lower_block(statements, ret, type_hint),
            ast::Expr::Lit(lit) => self.lower_lit(lit, type_hint),
            ast::Expr::Deref(expr) => self.lower_deref(expr, type_hint),
            ast::Expr::Ref(expr) => self.lower_ref(expr, type_hint),
            ast::Expr::Local(id) => self.lower_local(*id, type_hint),
            ast::Expr::Unary(op, inner) => self.lower_unary(*op, inner, type_hint),
            ast::Expr::Assign(lhs, rhs) => self.lower_assign(lhs, rhs, type_hint),
            ast::Expr::If(cond, then, els) => self.lower_if(cond, then, els, type_hint),
            ast::Expr::Cast(expr, typ) => self.lower_cast(expr, typ, type_hint),
            ast::Expr::Loop(body) => self.lower_loop(body, type_hint),
            ast::Expr::Binary(op, lhs, rhs) => self.lower_binary(*op, lhs, rhs, type_hint),
            ast::Expr::AssignOp(op, lhs, rhs) => self.lower_assign_op(*op, lhs, rhs, type_hint),
            ast::Expr::Break(value) => self.lower_break(*value, type_hint),
            ast::Expr::Continue => self.lower_continue(type_hint),
            ast::Expr::Tuple(exprs) => self.lower_tuple(exprs, type_hint),
            ast::Expr::TupleIndex(tup, index) => self.lower_tuple_index(tup, *index, type_hint),
            ast::Expr::Field(tup, field, _) => self.lower_field(tup, field, type_hint),
            ast::Expr::Call(func, args) => self.lower_call(func, args, type_hint),
            ast::Expr::EnumValue(typ, id) => self.lower_enum_value(typ, *id, type_hint),
            ast::Expr::Struct(func, initializers) => {
                self.lower_struct_expression(func, initializers, type_hint)
            }
            ast::Expr::Index(inner, index) => self.lower_index(inner, index, type_hint),
            ast::Expr::Return(inner) => self.lower_return(*inner, type_hint),
            ast::Expr::Fn(item, args) => self.lower_fn(item.clone(), *args, type_hint),
            _ => panic!("unimplemented {:?}", expr),
        };

        let result = match result {
            Ok(result) => result,
            Err(e) => {
                panic!("{:?} at {:?}", e, expr);
            }
        };

        Ok(result)
    }
}
