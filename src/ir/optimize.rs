use std::collections::HashSet;

use crate::{ast::BuiltinType, common::ArenaAllocatable};

use super::{builder::ExpressionBuilder, Expr, ExprKind, ExprP, IrCtx, IrId, Statement, Ty};

pub struct Optimizer<'ir> {
    ir: &'ir IrCtx<'ir>,
    builder: ExpressionBuilder<'ir>,
    used_ids: HashSet<IrId>,
}

impl<'ir> Optimizer<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            builder: ExpressionBuilder::new(ir),
            used_ids: HashSet::new(),
        }
    }

    pub fn is_used(&self, stmt: &Statement<'ir>) -> bool {
        match stmt {
            Statement::Label(id) => self.used_ids.contains(&id),
            Statement::LocalDef(id, _) => self.used_ids.contains(&id),
            _ => true,
        }
    }

    pub fn optimize_func_body(&mut self, expr: ExprP<'ir>) -> &'ir [Statement<'ir>] {
        let mut statements = Vec::new();
        let optimized = self.optimize_expr(expr);
        self.optimize_func_body_inner(optimized, &mut statements);
        statements.alloc_on(self.ir)
    }

    fn optimize_func_body_inner(&mut self, expr: ExprP<'ir>, statements: &mut Vec<Statement<'ir>>) {
        match expr.kind {
            ExprKind::Block(stmts, ret) => {
                statements.extend(stmts.iter().cloned());
                self.optimize_func_body_inner(ret, statements);
            }
            _ => {
                let statement = if expr.diverges() || expr.ty.is_void() {
                    Statement::Expression(expr)
                } else {
                    Statement::Expression(self.builder.ret(expr))
                };
                statements.push(statement);
            }
        }
    }

    pub fn optimize_expr(&mut self, expr: ExprP<'ir>) -> ExprP<'ir> {
        let builder = ExpressionBuilder::new(self.ir);

        match expr.kind {
            ExprKind::Local(_) if expr.ty.is_void() => self.builder.void(),
            ExprKind::Local(id) => {
                self.used_ids.insert(id);
                expr
            }
            ExprKind::Assign(l, r) if l.ty.is_void() => builder.block(
                [
                    Statement::Expression(self.optimize_expr(l)),
                    Statement::Expression(self.optimize_expr(r)),
                ],
                self.builder.void(),
            ),
            ExprKind::Assign(l, r) => builder.assign(self.optimize_expr(l), self.optimize_expr(r)),
            ExprKind::Block(stmts, ret) => {
                let mut new_stmts = Vec::new();
                for stmt in stmts {
                    if let Some(stmt) = self.optimize_stmt(stmt) {
                        new_stmts.push(stmt);
                    }
                }
                let ret = self.optimize_expr(ret);
                new_stmts.retain(|s| self.is_used(s));

                self.builder.block(new_stmts, ret)
            }
            ExprKind::Binary(op, lhs, rhs) => builder.binary(
                op,
                self.optimize_expr(lhs),
                self.optimize_expr(rhs),
                expr.ty,
            ),
            ExprKind::AssignOp(op, lhs, rhs) => {
                builder.assign_op(op, self.optimize_expr(lhs), self.optimize_expr(rhs))
            }
            ExprKind::Call(callee, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.optimize_expr(arg))
                    .collect::<Vec<_>>();

                Expr::rvalue(
                    ExprKind::Call(self.optimize_expr(callee), args.alloc_on(self.ir)),
                    expr.ty,
                )
                .alloc_on(self.ir)
            }

            ExprKind::Ref(inner) => builder.r#ref(self.optimize_expr(inner)),
            ExprKind::Deref(inner) if inner.ty.is_void() => builder.block(
                [Statement::Expression(self.optimize_expr(inner))],
                builder.void(),
            ),
            ExprKind::Deref(inner) => builder.deref(self.optimize_expr(inner)),
            ExprKind::Return(inner) if inner.ty.is_void() => builder.block(
                [Statement::Expression(self.optimize_expr(inner))],
                builder.void(),
            ),
            ExprKind::Return(inner) => {
                Expr::rvalue(ExprKind::Return(self.optimize_expr(inner)), expr.ty).alloc_on(self.ir)
            }

            ExprKind::Unary(op, inner) => builder.unary(op, self.optimize_expr(inner), expr.ty),

            ExprKind::If(cond, then, els) => Expr {
                is_const: expr.is_const,
                ty: expr.ty,
                kind: ExprKind::If(
                    self.optimize_expr(cond),
                    self.optimize_expr(then),
                    self.optimize_expr(els),
                ),
                value_type: expr.value_type,
            }
            .alloc_on(self.ir),
            ExprKind::Cast(inner) => builder.cast(self.optimize_expr(inner), expr.ty),
            ExprKind::Index(lhs, rhs) => {
                builder.index(self.optimize_expr(lhs), self.optimize_expr(rhs))
            }

            ExprKind::TupleIndex(lhs, _) if expr.ty.is_void() => builder.block(
                [Statement::Expression(self.optimize_expr(lhs))],
                self.builder.void(),
            ),
            ExprKind::Field(lhs, _) if expr.ty.is_void() => builder.block(
                [Statement::Expression(self.optimize_expr(lhs))],
                self.builder.void(),
            ),

            ExprKind::TupleIndex(lhs, idx) => {
                builder.tuple_index(self.optimize_expr(lhs), idx, expr.ty)
            }
            ExprKind::Field(lhs, id) => builder.field(self.optimize_expr(lhs), id, expr.ty),
            ExprKind::Fn(_) => expr,
            ExprKind::Lit(_) => expr,
            ExprKind::ConstValue(_) => expr,
            ExprKind::Unreachable => expr,
            ExprKind::Void => expr,
            ExprKind::Goto(label) => {
                self.used_ids.insert(label);
                expr
            }
        }
    }

    fn optimize_stmt(&mut self, stmt: &Statement<'ir>) -> Option<Statement<'ir>> {
        match stmt {
            Statement::Expression(expr) => Some(Statement::Expression(self.optimize_expr(expr))),
            Statement::LocalDef(_, ty) if ty.is_void() => None,
            _ => Some(stmt.clone()),
        }
    }
}
