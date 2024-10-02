use crate::ast::{BuiltinType, Span, UnOp};
use crate::common::{ice, AluminaError, ArenaAllocatable, CodeDiagnostic, HashMap, HashSet};
use crate::diagnostics::DiagnosticsStack;
use crate::ir::builder::{ExpressionBuilder, TypeBuilder};
use crate::ir::const_eval::LValue;
use crate::ir::const_eval::Value;
use crate::ir::{Expr, ExprKind, ExprP, FuncBody, Id, IrCtx, LocalDef, Statement, Ty, ValueType};
use crate::ir::{IntrinsicValueKind, Item};

// The purpose of ZST elider is to take all reads and writes of zero-sized types and
// replace them with ExprKind::Void or remove them altogether if the value is not used
// e.g. in a function call. Expressions of ZST type still remain in the IR but they are
// safe to ignore by codegen.
//
// It does some more specific fixups to the IR to make it ready for codegen. The resulting
// IR is generally not suitable for any further passes.
pub struct ZstElider<'ir> {
    ir: &'ir IrCtx<'ir>,
    diag: DiagnosticsStack,
    additional_locals: Vec<LocalDef<'ir>>,
    used_ids: HashSet<Id>,
}

impl<'ir> ZstElider<'ir> {
    pub fn new(diag: DiagnosticsStack, ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            diag,
            additional_locals: Vec::new(),
            used_ids: HashSet::default(),
        }
    }

    pub fn elide_zst_func_body(
        mut self,
        function_body: &FuncBody<'ir>,
    ) -> Result<(&'ir [LocalDef<'ir>], &'ir [Statement<'ir>]), AluminaError> {
        let builder = ExpressionBuilder::new(self.ir);
        let mut statements = Vec::new();

        match function_body.expr.kind {
            ExprKind::Block(stmts, ret) => {
                for stmt in stmts {
                    self.elide_zst_stmt(stmt, &mut statements)?;
                }
                self.elide_zst_stmt(
                    &Statement::Expression(builder.ret(ret, ret.span)),
                    &mut statements,
                )?;
            }
            _ => {
                self.elide_zst_stmt(
                    &Statement::Expression(
                        builder.ret(function_body.expr, function_body.expr.span),
                    ),
                    &mut statements,
                )?;
            }
        }

        let local_defs = function_body
            .local_defs
            .iter()
            .copied()
            .chain(self.additional_locals)
            .filter(|def| self.used_ids.remove(&def.id) && !def.ty.is_zero_sized())
            .collect::<Vec<_>>();

        Ok((local_defs.alloc_on(self.ir), statements.alloc_on(self.ir)))
    }

    pub fn elide_zst_expr(&mut self, expr: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let builder = ExpressionBuilder::new(self.ir);
        let types = TypeBuilder::new(self.ir);

        let _guard = self.diag.push_span(expr.span);

        let result = match expr.kind {
            ExprKind::Local(_) if expr.ty.is_zero_sized() => {
                builder.void(expr.ty, expr.value_type, expr.span)
            }
            ExprKind::Local(id) => {
                self.used_ids.insert(id);
                expr
            }
            ExprKind::Item(_) if expr.ty.is_zero_sized() => {
                builder.void(expr.ty, expr.value_type, expr.span)
            }
            ExprKind::Item(_) => expr,
            ExprKind::Assign(l, r) if l.ty.is_zero_sized() => {
                let l = self.elide_zst_expr(l)?;
                let r = self.elide_zst_expr(r)?;
                builder.block(
                    [Statement::Expression(l), Statement::Expression(r)],
                    builder.void(expr.ty, ValueType::RValue, expr.span),
                    expr.span,
                )
            }
            ExprKind::Assign(l, r) => {
                builder.assign(self.elide_zst_expr(l)?, self.elide_zst_expr(r)?, expr.span)
            }
            ExprKind::Block(stmts, ret) => {
                let mut statements = Vec::new();
                for stmt in stmts {
                    self.elide_zst_stmt(stmt, &mut statements)?;
                }

                let ret = self.elide_zst_expr(ret)?;
                statements.retain(|s| match s {
                    Statement::Label(id) => self.used_ids.contains(id),
                    _ => true,
                });
                builder.block(statements, ret, expr.span)
            }
            ExprKind::Binary(op, lhs, rhs) => builder.binary(
                op,
                self.elide_zst_expr(lhs)?,
                self.elide_zst_expr(rhs)?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Tuple(items) => {
                let mut statements = Vec::new();
                let mut inits = Vec::new();
                for arg in items.iter() {
                    let value = self.elide_zst_expr(arg.value)?;

                    if value.ty.is_zero_sized() {
                        statements.push(Statement::Expression(value));
                    } else {
                        inits.push((arg.index, value));
                    }
                }

                let ret = if expr.ty.is_zero_sized() {
                    builder.void(expr.ty, ValueType::RValue, expr.span)
                } else {
                    builder.tuple(inits, expr.ty, expr.span)
                };

                builder.block(statements, ret, expr.span)
            }
            ExprKind::Struct(fields) => {
                let mut statements = Vec::new();
                let mut inits = Vec::new();

                for arg in fields.iter() {
                    let value = self.elide_zst_expr(arg.value)?;

                    if value.ty.is_zero_sized() {
                        statements.push(Statement::Expression(value));
                    } else {
                        inits.push((arg.field, value));
                    }
                }

                let ret = if expr.ty.is_zero_sized() {
                    builder.void(expr.ty, ValueType::RValue, expr.span)
                } else {
                    builder.r#struct(inits, expr.ty, expr.span)
                };

                builder.block(statements, ret, expr.span)
            }
            ExprKind::Array(elems) => {
                if expr.ty.is_zero_sized() {
                    builder.block(
                        elems
                            .iter()
                            .map(|e| self.elide_zst_expr(e).map(Statement::Expression))
                            .collect::<Result<Vec<_>, _>>()?,
                        builder.void(expr.ty, expr.value_type, expr.span),
                        expr.span,
                    )
                } else {
                    builder.array(
                        elems
                            .iter()
                            .map(|e| self.elide_zst_expr(e))
                            .collect::<Result<Vec<_>, _>>()?,
                        expr.ty,
                        expr.span,
                    )
                }
            }
            ExprKind::AssignOp(op, lhs, rhs) => builder.assign_op(
                op,
                self.elide_zst_expr(lhs)?,
                self.elide_zst_expr(rhs)?,
                expr.span,
            ),
            ExprKind::Call(callee, args) => {
                // Functions that receive a zero-sized argument are a bit tricky. In order to be able
                // to replace the argument with a void expression, we need to evaluate the expression
                // that produce it beforehand. But we cannot just extract that single argument, since
                // we maintain a strict left-to-right evaluation order. So currently we bind all non-ZST
                // arguments as local variables and evaluate them in the order they appear in the call.
                // This is a bit pessimistic, but C compiler should still be able to optimize it away.
                let callee = self.elide_zst_expr(callee)?;
                let args = args
                    .iter()
                    .map(|arg| self.elide_zst_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                let extract_args = match callee.kind {
                    ExprKind::Intrinsic(_) => false,
                    _ => args.iter().any(|arg| arg.ty.is_zero_sized() && !arg.pure()),
                };

                if extract_args {
                    let mut statements = Vec::new();
                    let mut arguments = Vec::new();

                    for arg in args.iter() {
                        if arg.ty.is_zero_sized() {
                            statements.push(Statement::Expression(arg));
                            arguments.push(builder.void(arg.ty, arg.value_type, arg.span));
                        } else {
                            let id = self.ir.make_id();
                            self.additional_locals.push(LocalDef { id, ty: arg.ty });
                            self.used_ids.insert(id);
                            let local = builder.local(id, arg.ty, arg.span);
                            statements
                                .push(Statement::Expression(builder.assign(local, arg, arg.span)));
                            arguments.push(local);
                        }
                    }

                    builder.block(
                        statements,
                        Expr::rvalue(
                            ExprKind::Call(callee, arguments.alloc_on(self.ir)),
                            expr.ty,
                            expr.span,
                        )
                        .alloc_on(self.ir),
                        expr.span,
                    )
                } else {
                    Expr::rvalue(
                        ExprKind::Call(callee, args.alloc_on(self.ir)),
                        expr.ty,
                        expr.span,
                    )
                    .alloc_on(self.ir)
                }
            }
            ExprKind::Ref(inner) => {
                let inner = self.elide_zst_expr(inner)?;

                if inner.is_void() {
                    // Special case for mutiple pointers to void
                    builder.dangling(expr.ty, expr.span)
                } else if inner.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(inner)],
                        builder.dangling(expr.ty, expr.span),
                        expr.span,
                    )
                } else {
                    builder.r#ref(inner, expr.span)
                }
            }
            ExprKind::Deref(inner) => {
                let inner = self.elide_zst_expr(inner)?;
                if expr.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(inner)],
                        builder.void(expr.ty, expr.value_type, expr.span),
                        expr.span,
                    )
                } else {
                    builder.deref(inner, expr.span)
                }
            }
            ExprKind::Return(inner) => {
                let inner = self.elide_zst_expr(inner)?;
                if inner.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(inner)],
                        builder.ret(builder.void(expr.ty, expr.value_type, expr.span), expr.span),
                        expr.span,
                    )
                } else {
                    builder.ret(inner, expr.span)
                }
            }
            ExprKind::Unary(op, inner) => {
                builder.unary(op, self.elide_zst_expr(inner)?, expr.ty, expr.span)
            }
            ExprKind::If(cond, then, els, const_cond) => match const_cond {
                Some(true) => self.elide_zst_expr(then)?,
                Some(false) => self.elide_zst_expr(els)?,
                None => {
                    let cond = self.elide_zst_expr(cond)?;
                    let then = self.elide_zst_expr(then)?;
                    let els = self.elide_zst_expr(els)?;

                    match (then.ty.is_zero_sized(), els.ty.is_zero_sized()) {
                        (true, false) => builder.block(
                            [Statement::Expression(builder.if_then(
                                cond,
                                then,
                                builder.void(types.void(), ValueType::RValue, els.span),
                                None,
                                expr.span,
                            ))],
                            els,
                            expr.span,
                        ),
                        (false, true) => builder.block(
                            [Statement::Expression(builder.if_then(
                                builder.unary(
                                    UnOp::Not,
                                    cond,
                                    types.builtin(BuiltinType::Bool),
                                    cond.span,
                                ),
                                els,
                                builder.void(types.void(), ValueType::RValue, els.span),
                                None,
                                expr.span,
                            ))],
                            then,
                            expr.span,
                        ),
                        _ => builder.if_then(cond, then, els, None, expr.span),
                    }
                }
            },
            ExprKind::Cast(inner) => builder.cast(self.elide_zst_expr(inner)?, expr.ty, expr.span),
            ExprKind::Index(lhs, rhs) => {
                let indexee = self.elide_zst_expr(lhs)?;
                let index = self.elide_zst_expr(rhs)?;

                if !expr.ty.is_zero_sized() && indexee.ty.is_zero_sized() {
                    // Special case for indexing into a zero-length array of non-ZST elements
                    builder.block(
                        [Statement::Expression(indexee), Statement::Expression(index)],
                        builder.deref(
                            builder.dangling(types.pointer(expr.ty, expr.is_const), expr.span),
                            expr.span,
                        ),
                        expr.span,
                    )
                } else if expr.ty.is_zero_sized() {
                    builder.block(
                        [Statement::Expression(indexee), Statement::Expression(index)],
                        builder.void(expr.ty, expr.value_type, expr.span),
                        expr.span,
                    )
                } else {
                    builder.index(indexee, index, expr.span)
                }
            }

            ExprKind::TupleIndex(lhs, _) if expr.ty.is_zero_sized() => builder.block(
                [Statement::Expression(self.elide_zst_expr(lhs)?)],
                builder.void(expr.ty, expr.value_type, expr.span),
                expr.span,
            ),
            ExprKind::Field(lhs, _) if expr.ty.is_zero_sized() => builder.block(
                [Statement::Expression(self.elide_zst_expr(lhs)?)],
                builder.void(expr.ty, expr.value_type, expr.span),
                expr.span,
            ),
            ExprKind::TupleIndex(lhs, idx) => {
                builder.tuple_index(self.elide_zst_expr(lhs)?, idx, expr.ty, expr.span)
            }
            ExprKind::Field(lhs, id) => {
                builder.field(self.elide_zst_expr(lhs)?, id, expr.ty, expr.span)
            }
            ExprKind::Lit(v) => match v {
                Value::Array(elems) => {
                    let element_type = match expr.ty {
                        Ty::Array(ty, _) => ty,
                        _ => unreachable!(),
                    };
                    builder.array(
                        elems
                            .iter()
                            .map(|val| {
                                self.elide_zst_expr(builder.literal(*val, element_type, expr.span))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                        expr.ty,
                        expr.span,
                    )
                }
                Value::Tuple(elems) => {
                    let element_types = match expr.ty {
                        Ty::Tuple(tys) => tys,
                        _ => unreachable!(),
                    };

                    builder.tuple(
                        elems
                            .iter()
                            .zip(element_types.iter())
                            .enumerate()
                            .map(|(idx, (val, ty))| {
                                self.elide_zst_expr(builder.literal(*val, ty, expr.span))
                                    .map(|e| (idx, e))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                        expr.ty,
                        expr.span,
                    )
                }
                Value::Struct(fields) => {
                    let struct_like = match expr.ty {
                        Ty::Item(item) => match item.get().unwrap() {
                            Item::Closure(c) => &c.data,
                            Item::StructLike(s) => s,
                            _ => ice!(self.diag, "expected struct-like item"),
                        },
                        _ => ice!(self.diag, "expected struct-like item"),
                    };

                    let element_types: HashMap<_, _> =
                        struct_like.fields.iter().map(|f| (f.id, f.ty)).collect();

                    builder.r#struct(
                        fields
                            .iter()
                            .map(|(id, val)| {
                                self.elide_zst_expr(builder.literal(
                                    *val,
                                    element_types[id],
                                    expr.span,
                                ))
                                .map(|e| (*id, e))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                        expr.ty,
                        expr.span,
                    )
                }
                Value::FunctionPointer(item) => {
                    builder.cast(builder.function(item, expr.span), expr.ty, expr.span)
                }
                Value::Uninitialized if expr.ty.is_zero_sized() => {
                    builder.void(expr.ty, ValueType::RValue, expr.span)
                }
                Value::Pointer(lvalue, _) => {
                    let lvalue_expr = self.elide_zst_lvalue(&lvalue, expr.span);
                    self.elide_zst_expr(builder.r#ref(lvalue_expr, expr.span))?
                }
                Value::Void => builder.void(expr.ty, ValueType::RValue, expr.span),

                _ => expr,
            },
            ExprKind::Unreachable => expr,
            ExprKind::Nop => expr,
            ExprKind::Intrinsic(ref kind) => match kind {
                IntrinsicValueKind::Uninitialized if expr.ty.is_zero_sized() => {
                    builder.void(expr.ty, ValueType::RValue, expr.span)
                }
                IntrinsicValueKind::Transmute(inner) if expr.ty.is_zero_sized() => builder.block(
                    [Statement::Expression(self.elide_zst_expr(inner)?)],
                    builder.void(expr.ty, expr.value_type, expr.span),
                    expr.span,
                ),
                IntrinsicValueKind::Transmute(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Transmute(self.elide_zst_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::Volatile(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Volatile(self.elide_zst_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::StopIteration | IntrinsicValueKind::ConstPanic(_) => {
                    builder.unreachable(expr.span)
                }
                IntrinsicValueKind::ConstAlloc(_, size) => builder.block(
                    [Statement::Expression(self.elide_zst_expr(size)?)],
                    builder.literal(Value::USize(0), expr.ty, expr.span),
                    expr.span,
                ),
                IntrinsicValueKind::ConstWrite(inner, _) | IntrinsicValueKind::ConstFree(inner) => {
                    builder.block(
                        [Statement::Expression(self.elide_zst_expr(inner)?)],
                        builder.void(expr.ty, expr.value_type, expr.span),
                        expr.span,
                    )
                }
                _ => expr,
            },
            ExprKind::Goto(label) => {
                self.used_ids.insert(label);
                expr
            }
            ExprKind::Tag(tag, inner) => {
                match tag {
                    "const_only" => self.diag.warn(CodeDiagnostic::ConstOnly),
                    _ => {}
                }
                builder.tag(tag, self.elide_zst_expr(inner)?, expr.span)
            }
        };

        // Some C-codegen specific fixups

        // Named function types are unit types, hence ZSTs, and will get elided away if e.g. stored
        // in variables, passed as arguments, ... If this happens, we still need to make sure that
        // codegen invokes it correctly.
        if let crate::ir::Ty::Item(item) = result.ty {
            if let Item::Function(_) = item.get().unwrap() {
                if result.is_void() {
                    return Ok(builder.function(item, expr.span));
                }
            }
        }

        if result.is_void() && result.ty.is_never() {
            return Ok(builder.unreachable(expr.span));
        }

        Ok(result)
    }

    fn elide_zst_lvalue(&mut self, value: &LValue<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let builder = ExpressionBuilder::new(self.ir);

        match value {
            LValue::Const(item) => {
                let r#const = item.get_const().unwrap();
                builder.const_var(item, r#const.ty, span)
            }
            LValue::Variable(_) => unreachable!(),
            LValue::Field(inner, field) => {
                let inner_expr = self.elide_zst_lvalue(inner, span);
                if let Ty::Item(item) = inner_expr.ty {
                    if let Item::StructLike(struct_like) = item.get().unwrap() {
                        let field_type = struct_like
                            .fields
                            .iter()
                            .find(|f| f.id == *field)
                            .unwrap()
                            .ty;
                        return builder.field(inner_expr, *field, field_type, span);
                    }
                }
                unreachable!()
            }
            LValue::Index(inner, idx) => {
                let inner_expr = self.elide_zst_lvalue(inner, span);
                builder.const_index(inner_expr, *idx, span)
            }
            LValue::TupleIndex(inner, idx) => {
                let inner_expr = self.elide_zst_lvalue(inner, span);
                if let Ty::Tuple(tys) = inner_expr.ty {
                    return builder.tuple_index(inner_expr, *idx, tys[*idx], span);
                }
                unreachable!()
            }
            LValue::Alloc(_) => unreachable!(),
        }
    }

    fn elide_zst_stmt(
        &mut self,
        stmt: &Statement<'ir>,
        statements: &mut Vec<Statement<'ir>>,
    ) -> Result<(), AluminaError> {
        match stmt {
            Statement::Expression(expr) => {
                let expr = self.elide_zst_expr(expr)?;
                if expr.is_void() {
                    return Ok(());
                }

                if expr.pure() {
                    return Ok(());
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

        Ok(())
    }
}
