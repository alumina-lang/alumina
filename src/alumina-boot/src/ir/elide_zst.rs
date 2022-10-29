use std::collections::{HashMap, HashSet};

use crate::{
    ast::{BuiltinType, UnOp},
    common::ArenaAllocatable,
    intrinsics::CodegenIntrinsicKind,
    ir::ValueType,
};

use super::{
    builder::{ExpressionBuilder, TypeBuilder},
    const_eval::Value,
    Expr, ExprKind, ExprP, FuncBody, IrCtx, IrId, Lit, LocalDef, Statement, Ty, UnqualifiedKind,
};

// The purpose of ZST elider is to take all reads and writes of zero-sized types and
// replace them with ExprKind::Void or remove them altogether if the value is not used
// e.g. in a function call. Expressions of ZST type still remain in the IR but they are
// safe to ignore by codegen.
pub struct ZstElider<'ir> {
    ir: &'ir IrCtx<'ir>,
    additional_locals: Vec<LocalDef<'ir>>,
    used_ids: HashSet<IrId>,
}

impl<'ir> ZstElider<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            additional_locals: Vec::new(),
            used_ids: HashSet::new(),
        }
    }

    pub fn elide_zst_func_body(mut self, function_body: FuncBody<'ir>) -> FuncBody<'ir> {
        let mut statements = Vec::new();
        for stmt in function_body.statements {
            self.elide_zst_stmt(stmt, &mut statements);
        }

        let local_defs = function_body
            .local_defs
            .iter()
            .copied()
            .filter(|def| self.used_ids.contains(&def.id) && !def.typ.is_zero_sized())
            .chain(self.additional_locals.into_iter())
            .collect::<Vec<_>>();

        FuncBody {
            statements: statements.alloc_on(self.ir),
            local_defs: local_defs.alloc_on(self.ir),
            raw_body: function_body.raw_body,
        }
    }

    pub fn elide_zst_expr(&mut self, expr: ExprP<'ir>) -> ExprP<'ir> {
        let builder = ExpressionBuilder::new(self.ir);
        let types = TypeBuilder::new(self.ir);

        let result = match expr.kind {
            ExprKind::Local(_) if expr.ty.is_zero_sized() => builder.void(expr.ty, expr.value_type),
            ExprKind::Local(id) => {
                self.used_ids.insert(id);
                expr
            }
            ExprKind::Static(_) | ExprKind::Const(_) if expr.ty.is_zero_sized() => {
                builder.void(expr.ty, expr.value_type)
            }
            ExprKind::Static(_) | ExprKind::Const(_) => expr,
            ExprKind::Assign(l, r) if l.ty.is_zero_sized() => {
                let l = self.elide_zst_expr(l);
                let r = self.elide_zst_expr(r);
                builder.block(
                    [Statement::Expression(l), Statement::Expression(r)],
                    builder.void(expr.ty, ValueType::RValue),
                )
            }
            ExprKind::Assign(l, r) => {
                builder.assign(self.elide_zst_expr(l), self.elide_zst_expr(r))
            }
            ExprKind::Block(stmts, ret) => {
                let mut statements = Vec::new();
                for stmt in stmts {
                    self.elide_zst_stmt(stmt, &mut statements);
                }

                let ret = self.elide_zst_expr(ret);
                statements.retain(|s| match s {
                    Statement::Label(id) => self.used_ids.contains(id),
                    _ => true,
                });
                builder.block(statements, ret)
            }
            ExprKind::Binary(op, lhs, rhs) => builder.binary(
                op,
                self.elide_zst_expr(lhs),
                self.elide_zst_expr(rhs),
                expr.ty,
            ),
            ExprKind::Tuple(items) => {
                let mut statements = Vec::new();
                let mut inits = Vec::new();
                for arg in items.iter() {
                    let value = self.elide_zst_expr(arg.value);

                    if value.ty.is_zero_sized() {
                        statements.push(Statement::Expression(value));
                    } else {
                        inits.push((arg.index, value));
                    }
                }

                let ret = if expr.ty.is_zero_sized() {
                    builder.void(expr.ty, ValueType::RValue)
                } else {
                    builder.tuple(inits, expr.ty)
                };

                builder.block(statements, ret)
            }
            ExprKind::Struct(fields) => {
                let mut statements = Vec::new();
                let mut inits = Vec::new();

                for arg in fields.iter() {
                    let value = self.elide_zst_expr(arg.value);

                    if value.ty.is_zero_sized() {
                        statements.push(Statement::Expression(value));
                    } else {
                        inits.push((arg.field, value));
                    }
                }

                let ret = if expr.ty.is_zero_sized() {
                    builder.void(expr.ty, ValueType::RValue)
                } else {
                    builder.r#struct(inits, expr.ty)
                };

                builder.block(statements, ret)
            }
            ExprKind::Array(elems) => {
                if expr.ty.is_zero_sized() {
                    builder.block(
                        elems
                            .iter()
                            .map(|e| Statement::Expression(self.elide_zst_expr(*e))),
                        builder.void(expr.ty, expr.value_type),
                    )
                } else {
                    builder.array(elems.iter().map(|e| self.elide_zst_expr(*e)), expr.ty)
                }
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                builder.assign_op(op, self.elide_zst_expr(lhs), self.elide_zst_expr(rhs))
            }
            ExprKind::Call(callee, args) => {
                // Functions that receive a zero-sized argument are a bit tricky. In order to be able
                // to replace the argument with a void expression, we need to evaluate the expression
                // that produce it beforehand. But we cannot just extract that single argument, since
                // we maintain a strict left-to-right evaluation order. So currently we bind all non-ZST
                // arguments as local variables and evaluate them in the order they appear in the call.
                // This is a bit pessimistic, but C compiler should still be able to optimize it away.
                let callee = self.elide_zst_expr(callee);
                let args = args
                    .iter()
                    .map(|arg| self.elide_zst_expr(arg))
                    .collect::<Vec<_>>();

                let extract_args = match callee.kind {
                    ExprKind::CodegenIntrinsic(_) => false,
                    _ => args.iter().any(|arg| arg.ty.is_zero_sized() && !arg.pure()),
                };

                if extract_args {
                    let mut statements = Vec::new();
                    let mut arguments = Vec::new();

                    for arg in args.iter() {
                        if arg.ty.is_zero_sized() {
                            statements.push(Statement::Expression(arg));
                            arguments.push(builder.void(arg.ty, arg.value_type));
                        } else {
                            let id = self.ir.make_id();
                            self.additional_locals.push(LocalDef { id, typ: arg.ty });
                            let local = builder.local(id, arg.ty);
                            statements.push(Statement::Expression(builder.assign(local, arg)));
                            arguments.push(builder.local(id, arg.ty));
                        }
                    }

                    builder.block(
                        statements,
                        Expr::rvalue(ExprKind::Call(callee, arguments.alloc_on(self.ir)), expr.ty)
                            .alloc_on(self.ir),
                    )
                } else {
                    Expr::rvalue(ExprKind::Call(callee, args.alloc_on(self.ir)), expr.ty)
                        .alloc_on(self.ir)
                }
            }
            ExprKind::Ref(inner) => {
                let inner = self.elide_zst_expr(inner);

                if inner.is_void() {
                    // Special case for mutiple pointers to void
                    builder.lit(Lit::Int(0), expr.ty)
                } else if inner.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(inner)],
                        builder.lit(Lit::Int(0), expr.ty),
                    )
                } else {
                    builder.r#ref(inner)
                }
            }
            ExprKind::Deref(inner) => {
                let inner = self.elide_zst_expr(inner);
                if expr.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(inner)],
                        builder.void(expr.ty, expr.value_type),
                    )
                } else {
                    builder.deref(inner)
                }
            }
            ExprKind::Return(inner) => {
                let inner = self.elide_zst_expr(inner);
                if inner.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(inner)],
                        builder.ret(builder.void(expr.ty, expr.value_type)),
                    )
                } else {
                    builder.ret(inner)
                }
            }
            ExprKind::Unary(op, inner) => builder.unary(op, self.elide_zst_expr(inner), expr.ty),
            ExprKind::If(cond, then, els) => {
                let cond = self.elide_zst_expr(cond);
                let then = self.elide_zst_expr(then);
                let els = self.elide_zst_expr(els);

                match (then.ty.is_zero_sized(), els.ty.is_zero_sized()) {
                    (true, false) => builder.block(
                        [Statement::Expression(builder.if_then(
                            cond,
                            then,
                            builder.void(types.builtin(BuiltinType::Void), ValueType::RValue),
                        ))],
                        els,
                    ),
                    (false, true) => builder.block(
                        [Statement::Expression(builder.if_then(
                            builder.unary(UnOp::Not, cond, types.builtin(BuiltinType::Bool)),
                            els,
                            builder.void(types.builtin(BuiltinType::Void), ValueType::RValue),
                        ))],
                        then,
                    ),
                    _ => builder.if_then(cond, then, els),
                }
            }
            ExprKind::Cast(inner) => builder.cast(self.elide_zst_expr(inner), expr.ty),
            ExprKind::Index(lhs, rhs) => {
                let indexee = self.elide_zst_expr(lhs);
                let index = self.elide_zst_expr(rhs);

                if indexee.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(indexee), Statement::Expression(index)],
                        builder.void(expr.ty, expr.value_type),
                    )
                } else {
                    builder.index(indexee, index)
                }
            }

            ExprKind::TupleIndex(lhs, _) if expr.ty.is_zero_sized() => builder.block(
                [Statement::Expression(self.elide_zst_expr(lhs))],
                builder.void(expr.ty, expr.value_type),
            ),
            ExprKind::Field(lhs, _) if expr.ty.is_zero_sized() => builder.block(
                [Statement::Expression(self.elide_zst_expr(lhs))],
                builder.void(expr.ty, expr.value_type),
            ),
            ExprKind::TupleIndex(lhs, idx) => {
                builder.tuple_index(self.elide_zst_expr(lhs), idx, expr.ty)
            }
            ExprKind::Field(lhs, id) => builder.field(self.elide_zst_expr(lhs), id, expr.ty),
            ExprKind::Fn(_) => expr,
            ExprKind::Lit(_) => expr,
            ExprKind::ConstValue(v) => match v {
                Value::Array(elems) => {
                    let element_type = match expr.ty {
                        Ty::Array(ty, _) => ty,
                        _ => unreachable!(),
                    };

                    builder.array(
                        elems.iter().map(|val| {
                            self.elide_zst_expr(builder.const_value(*val, element_type))
                        }),
                        expr.ty,
                    )
                }
                Value::Tuple(elems) => {
                    let element_types = match expr.ty {
                        Ty::Tuple(tys) => tys,
                        _ => unreachable!(),
                    };

                    builder.tuple(
                        elems.iter().zip(element_types.iter()).enumerate().map(
                            |(idx, (val, ty))| {
                                (idx, self.elide_zst_expr(builder.const_value(*val, *ty)))
                            },
                        ),
                        expr.ty,
                    )
                }
                Value::Struct(fields) => {
                    let element_types: HashMap<_, _> = match expr.ty {
                        Ty::NamedType(item) => item
                            .get_struct_like()
                            .unwrap()
                            .fields
                            .iter()
                            .map(|f| (f.id, f.ty))
                            .collect(),
                        _ => unreachable!(),
                    };

                    builder.r#struct(
                        fields.iter().map(|(id, val)| {
                            (
                                *id,
                                self.elide_zst_expr(builder.const_value(*val, element_types[id])),
                            )
                        }),
                        expr.ty,
                    )
                }
                _ => expr,
            },
            ExprKind::Unreachable => expr,
            ExprKind::Void => expr,
            ExprKind::CodegenIntrinsic(ref kind) => match kind {
                CodegenIntrinsicKind::Uninitialized if expr.ty.is_zero_sized() => {
                    builder.void(expr.ty, ValueType::RValue)
                }
                _ => expr,
            },
            ExprKind::Goto(label) => {
                self.used_ids.insert(label);
                expr
            }
        };

        // Some C-codegen specific fixups

        // Named function types are unit types, hence ZSTs, and will get elided away if e.g. stored
        // in variables, passed as arguments, ... If this happens, we still need to make sure that
        // codegen invokes it correctly.
        if let crate::ir::Ty::NamedFunction(item) = result.ty {
            if result.is_void() {
                return builder.function(item);
            }
        }

        if result.is_void() && result.ty.is_never() {
            return builder.unreachable();
        }

        // At this point unqualified strings are only present as arguments to the string constructor. They are always
        // `&u8`.
        if let Ty::Unqualified(UnqualifiedKind::String(_)) = result.ty {
            return Expr {
                is_const: result.is_const,
                ty: types.pointer(types.builtin(BuiltinType::U8), true),
                value_type: result.value_type,
                kind: result.kind.clone(),
            }
            .alloc_on(self.ir);
        }

        result
    }

    fn elide_zst_stmt(&mut self, stmt: &Statement<'ir>, statements: &mut Vec<Statement<'ir>>) {
        match stmt {
            Statement::Expression(expr) => {
                let expr = self.elide_zst_expr(expr);
                if expr.is_void() {
                    return;
                }

                if expr.pure() {
                    return;
                }

                // Reduce nesting of void blocks
                if let ExprKind::Block(stmts, ret) = expr.kind {
                    for stmt in stmts {
                        statements.push(stmt.clone());
                    }
                    statements.push(Statement::Expression(ret));
                } else {
                    statements.push(Statement::Expression(expr));
                }
            }
            _ => statements.push(stmt.clone()),
        }
    }
}
