use core::panic;

use crate::{ast::BuiltinType, common::ArenaAllocatable, ir::*};

use super::const_eval::Value;

pub struct ExpressionBuilder<'ir> {
    ir: &'ir IrCtx<'ir>,
}

impl<'ir> ExpressionBuilder<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self { ir }
    }

    pub fn local(&self, id: IrId, typ: TyP<'ir>) -> ExprP<'ir> {
        Expr::lvalue(ExprKind::Local(id), typ).alloc_on(self.ir)
    }

    fn fill_block(
        &self,
        target: &mut Vec<Statement<'ir>>,
        iter: impl IntoIterator<Item = Statement<'ir>>,
    ) -> Result<(), ExprP<'ir>> {
        use ExprKind::*;
        use Statement::*;

        let mut iter = iter.into_iter();
        'outer: loop {
            match iter.next() {
                Some(Expression(expr)) if expr.diverges() => {
                    while let Some(stmt) = iter.next() {
                        match stmt {
                            // If there is a label after an unreachable expression, the remainder might not
                            // actually be unreachable, as something might jump to it
                            Label(_) => {
                                target.push(Expression(expr));
                                target.push(stmt);
                                continue 'outer;
                            }
                            _ => {}
                        }
                    }
                    return Err(expr);
                }
                Some(Expression(Expr {
                    kind: Block(stmts, ret),
                    ..
                })) => {
                    self.fill_block(target, stmts.into_iter().cloned())?;
                    target.push(Expression(ret))
                }
                Some(Expression(expr)) if expr.pure() => {}
                Some(stmt) => target.push(stmt),
                None => break,
            }
        }

        Ok(())
    }

    pub fn block(
        &self,
        statements: impl IntoIterator<Item = Statement<'ir>>,
        ret: ExprP<'ir>,
    ) -> ExprP<'ir> {
        let mut merged = Vec::new();

        let ret = match self.fill_block(&mut merged, statements.into_iter()) {
            Ok(()) => ret,
            Err(expr) => expr,
        };

        if merged.is_empty() {
            return ret;
        }

        Expr::rvalue(ExprKind::Block(merged.alloc_on(self.ir), ret), ret.ty).alloc_on(self.ir)
    }

    pub fn call<I>(&self, callee: ExprP<'ir>, args: I, return_ty: TyP<'ir>) -> ExprP<'ir>
    where
        I: IntoIterator<Item = ExprP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let result = Expr::rvalue(
            ExprKind::Call(callee, self.ir.arena.alloc_slice_fill_iter(args)),
            return_ty,
        );

        result.alloc_on(self.ir)
    }

    pub fn lit(&self, lit: Lit<'ir>, ty: TyP<'ir>) -> ExprP<'ir> {
        Expr::rvalue(ExprKind::Lit(lit), ty).alloc_on(self.ir)
    }

    pub fn diverges(&self, exprs: impl IntoIterator<Item = ExprP<'ir>>) -> ExprP<'ir> {
        let block = self.block(
            exprs.into_iter().map(|expr| Statement::Expression(expr)),
            self.void(),
        );

        // This is a bit of hack, helper function for blocks that diverge. To simplify the caller's code,
        // we accept any block (can contain excess) and if it doesn't actually diverge, we panic here.
        assert!(block.diverges());

        block
    }

    pub fn assign(&self, lhs: ExprP<'ir>, rhs: ExprP<'ir>) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Assign(lhs, rhs),
            self.ir.intern_type(Ty::Builtin(BuiltinType::Void)),
        )
        .alloc_on(self.ir)
    }

    pub fn goto(&self, label: IrId) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Goto(label),
            self.ir.intern_type(Ty::Builtin(BuiltinType::Never)),
        )
        .alloc_on(self.ir)
    }

    pub fn assign_op(&self, op: BinOp, lhs: ExprP<'ir>, rhs: ExprP<'ir>) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::AssignOp(op, lhs, rhs),
            self.ir.intern_type(Ty::Builtin(BuiltinType::Void)),
        )
        .alloc_on(self.ir)
    }

    pub fn void(&self) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Void,
            self.ir.intern_type(Ty::Builtin(BuiltinType::Void)),
        )
        .alloc_on(self.ir)
    }

    pub fn function(&self, item: IRItemP<'ir>) -> ExprP<'ir> {
        let func = item.get_function();
        let args: Vec<_> = func.args.iter().map(|arg| arg.ty).collect();
        let ty = Ty::Fn(args.alloc_on(self.ir), func.return_type);

        Expr::const_lvalue(ExprKind::Fn(item), self.ir.intern_type(ty)).alloc_on(self.ir)
    }

    pub fn unreachable(&self) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Unreachable,
            self.ir.intern_type(Ty::Builtin(BuiltinType::Never)),
        )
        .alloc_on(self.ir)
    }

    pub fn tuple_index(&self, tuple: ExprP<'ir>, index: usize, typ: TyP<'ir>) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::TupleIndex(tuple, index),
            value_type: tuple.value_type,
            is_const: tuple.is_const,
            ty: typ,
        };

        expr.alloc_on(self.ir)
    }

    pub fn const_value(&self, val: Value) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::ConstValue(val),
            value_type: ValueType::RValue,
            is_const: true,
            ty: self.ir.intern_type(Ty::Builtin(val.type_kind())),
        };

        expr.alloc_on(self.ir)
    }

    pub fn deref(&self, inner: ExprP<'ir>) -> ExprP<'ir> {
        let result = match inner.ty {
            Ty::Pointer(ty, false) => Expr::lvalue(ExprKind::Deref(inner), ty),
            Ty::Pointer(ty, true) => Expr::const_lvalue(ExprKind::Deref(inner), ty),
            _ => panic!("not a pointer"),
        };

        result.alloc_on(self.ir)
    }

    pub fn binary(
        &self,
        op: BinOp,
        lhs: ExprP<'ir>,
        rhs: ExprP<'ir>,
        result_typ: TyP<'ir>,
    ) -> ExprP<'ir> {
        let result = Expr::rvalue(ExprKind::Binary(op, lhs, rhs), result_typ);

        result.alloc_on(self.ir)
    }

    pub fn ret(&self, inner: ExprP<'ir>) -> ExprP<'ir> {
        let result = Expr::rvalue(
            ExprKind::Return(inner),
            self.ir.intern_type(Ty::Builtin(BuiltinType::Never)),
        );

        result.alloc_on(self.ir)
    }

    pub fn cast(&self, expr: ExprP<'ir>, typ: TyP<'ir>) -> ExprP<'ir> {
        let result = Expr::rvalue(ExprKind::Cast(expr), typ);

        result.alloc_on(self.ir)
    }

    pub fn unary(&self, op: UnOp, inner: ExprP<'ir>, result_typ: TyP<'ir>) -> ExprP<'ir> {
        let result = Expr::rvalue(ExprKind::Unary(op, inner), result_typ);

        result.alloc_on(self.ir)
    }

    pub fn r#ref(&self, inner: ExprP<'ir>) -> ExprP<'ir> {
        assert!(matches!(inner.value_type, ValueType::LValue));

        let result = Expr::rvalue(
            ExprKind::Ref(inner),
            self.ir.intern_type(Ty::Pointer(inner.ty, inner.is_const)),
        );

        result.alloc_on(self.ir)
    }

    pub fn index(&self, inner: ExprP<'ir>, index: ExprP<'ir>) -> ExprP<'ir> {
        let kind = ExprKind::Index(inner, index);
        let result = match inner.ty {
            Ty::Pointer(ty, false) => Expr::lvalue(kind, ty),
            Ty::Pointer(ty, true) => Expr::const_lvalue(kind, ty),
            Ty::Array(ty, _) if !inner.is_const => Expr::lvalue(kind, ty),
            Ty::Array(ty, _) if inner.is_const => Expr::const_lvalue(kind, ty),
            _ => panic!("cannot index"),
        };

        result.alloc_on(self.ir)
    }

    pub fn field(&self, obj: ExprP<'ir>, field_id: IrId, typ: TyP<'ir>) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::Field(obj, field_id),
            value_type: obj.value_type,
            is_const: obj.is_const,
            ty: typ,
        };

        expr.alloc_on(self.ir)
    }
}
