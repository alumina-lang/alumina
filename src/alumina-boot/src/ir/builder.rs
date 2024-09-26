use crate::ast::BuiltinType;
use crate::common::ArenaAllocatable;
use crate::ir::const_eval::Value;
use crate::ir::*;

#[derive(Clone)]
pub struct ExpressionBuilder<'ir> {
    ir: &'ir IrCtx<'ir>,
}

impl<'ir> ExpressionBuilder<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self { ir }
    }

    pub fn local(&self, id: Id, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        Expr::lvalue(ExprKind::Local(id), ty, span).alloc_on(self.ir)
    }

    pub fn static_var(&self, item: ItemP<'ir>, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        Expr::lvalue(ExprKind::Item(item), ty, span).alloc_on(self.ir)
    }

    pub fn const_var(&self, item: ItemP<'ir>, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        Expr::const_lvalue(ExprKind::Item(item), ty, span).alloc_on(self.ir)
    }

    fn fill_block(
        target: &mut Vec<Statement<'ir>>,
        iter: impl IntoIterator<Item = Statement<'ir>>,
    ) -> Result<(), ExprP<'ir>> {
        use ExprKind::*;
        use Statement::*;

        let mut iter = iter.into_iter();
        'outer: loop {
            match iter.next() {
                Some(Expression(expr)) if expr.diverges() => {
                    for stmt in iter.by_ref() {
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
                    Self::fill_block(target, stmts.iter().cloned())?;
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
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let mut merged = Vec::new();

        let ret = match Self::fill_block(&mut merged, statements) {
            Ok(()) => ret,
            Err(expr) => expr,
        };

        if merged.is_empty() {
            return ret;
        }

        Expr::rvalue(ExprKind::Block(merged.alloc_on(self.ir), ret), ret.ty, span).alloc_on(self.ir)
    }

    pub fn call<I>(
        &self,
        callee: ExprP<'ir>,
        args: I,
        return_ty: TyP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir>
    where
        I: IntoIterator<Item = ExprP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let result = Expr::rvalue(
            ExprKind::Call(callee, self.ir.arena.alloc_slice_fill_iter(args)),
            return_ty,
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn array<I>(&self, args: I, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir>
    where
        I: IntoIterator<Item = ExprP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let result = Expr::rvalue(
            ExprKind::Array(self.ir.arena.alloc_slice_fill_iter(args)),
            ty,
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn tuple<I>(&self, args: I, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir>
    where
        I: IntoIterator<Item = (usize, ExprP<'ir>)>,
        I::IntoIter: ExactSizeIterator,
    {
        let result = Expr::rvalue(
            ExprKind::Tuple(
                self.ir.arena.alloc_slice_fill_iter(
                    args.into_iter()
                        .map(|(index, value)| super::TupleInit { index, value }),
                ),
            ),
            ty,
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn r#struct<I>(&self, args: I, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir>
    where
        I: IntoIterator<Item = (Id, ExprP<'ir>)>,
        I::IntoIter: ExactSizeIterator,
    {
        let result = Expr::rvalue(
            ExprKind::Struct(
                self.ir.arena.alloc_slice_fill_iter(
                    args.into_iter()
                        .map(|(field, value)| super::StructInit { field, value }),
                ),
            ),
            ty,
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn if_then(
        &self,
        cond: ExprP<'ir>,
        then: ExprP<'ir>,
        els: ExprP<'ir>,
        const_cond: Option<bool>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let result = Expr::rvalue(
            ExprKind::If(cond, then, els, const_cond),
            self.ir.intern_type(Ty::gcd(then.ty, els.ty)),
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn codegen_intrinsic(
        &self,
        kind: IntrinsicValueKind<'ir>,
        ty: TyP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        Expr::rvalue(ExprKind::Intrinsic(kind), ty, span).alloc_on(self.ir)
    }

    pub fn diverges(
        &self,
        exprs: impl IntoIterator<Item = ExprP<'ir>>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let block = self.block(
            exprs.into_iter().map(Statement::Expression),
            self.void(self.ir.intern_type(Ty::void()), ValueType::RValue, span),
            span,
        );

        // This is a bit of hack, helper function for blocks that diverge. To simplify the caller's code,
        // we accept any block (can contain excess) and if it doesn't actually diverge, we panic here.
        assert!(block.diverges());

        block
    }

    pub fn assign(&self, lhs: ExprP<'ir>, rhs: ExprP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Assign(lhs, rhs),
            self.ir.intern_type(Ty::void()),
            span,
        )
        .alloc_on(self.ir)
    }

    pub fn goto(&self, label: Id, span: Option<Span>) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Goto(label),
            self.ir.intern_type(Ty::Builtin(BuiltinType::Never)),
            span,
        )
        .alloc_on(self.ir)
    }

    pub fn assign_op(
        &self,
        op: BinOp,
        lhs: ExprP<'ir>,
        rhs: ExprP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::AssignOp(op, lhs, rhs),
            self.ir.intern_type(Ty::void()),
            span,
        )
        .alloc_on(self.ir)
    }

    pub fn void(&self, ty: TyP<'ir>, value_type: ValueType, span: Option<Span>) -> ExprP<'ir> {
        Expr {
            kind: ExprKind::Nop,
            value_type,
            is_const: true,
            ty,
            span,
        }
        .alloc_on(self.ir)
    }

    pub fn function(&self, item: ItemP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        Expr::const_lvalue(
            ExprKind::Item(item),
            self.ir.intern_type(Ty::Item(item)),
            span,
        )
        .alloc_on(self.ir)
    }

    pub fn unreachable(&self, span: Option<Span>) -> ExprP<'ir> {
        Expr::rvalue(
            ExprKind::Unreachable,
            self.ir.intern_type(Ty::Builtin(BuiltinType::Never)),
            span,
        )
        .alloc_on(self.ir)
    }

    pub fn tuple_index(
        &self,
        tuple: ExprP<'ir>,
        index: usize,
        ty: TyP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::TupleIndex(tuple, index),
            value_type: tuple.value_type,
            is_const: tuple.is_const,
            ty,
            span,
        };

        expr.alloc_on(self.ir)
    }

    pub fn tag(&self, tag: &'_ str, inner: ExprP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::Tag(self.ir.intern_str(tag), inner),
            value_type: inner.value_type,
            is_const: inner.is_const,
            ty: inner.ty,
            span,
        };

        expr.alloc_on(self.ir)
    }

    pub fn dangling(&self, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        if let Ty::Pointer(inner, _) = ty {
            self.codegen_intrinsic(IntrinsicValueKind::Dangling(inner), ty, span)
        } else {
            unreachable!()
        }
    }

    pub fn literal(&self, val: Value<'ir>, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::Lit(val),
            value_type: ValueType::RValue,
            is_const: true,
            ty,
            span,
        };

        expr.alloc_on(self.ir)
    }

    pub fn deref(&self, inner: ExprP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        // optimize away ref followed by deref
        match inner.kind {
            ExprKind::Ref(inner) => return inner,
            _ => {}
        };

        let result = match inner.ty {
            Ty::Pointer(ty, false) => Expr::lvalue(ExprKind::Deref(inner), ty, span),
            Ty::Pointer(ty, true) => Expr::const_lvalue(ExprKind::Deref(inner), ty, span),
            _ => panic!("not a pointer"),
        };

        result.alloc_on(self.ir)
    }

    pub fn binary(
        &self,
        op: BinOp,
        lhs: ExprP<'ir>,
        rhs: ExprP<'ir>,
        result_ty: TyP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let result = Expr::rvalue(ExprKind::Binary(op, lhs, rhs), result_ty, span);

        result.alloc_on(self.ir)
    }

    pub fn ret(&self, inner: ExprP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let result = Expr::rvalue(
            ExprKind::Return(inner),
            self.ir.intern_type(Ty::Builtin(BuiltinType::Never)),
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn cast(&self, expr: ExprP<'ir>, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let result = Expr::rvalue(ExprKind::Cast(expr), ty, span);

        result.alloc_on(self.ir)
    }

    pub fn coerce(&self, expr: ExprP<'ir>, ty: TyP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let result = Expr {
            is_const: expr.is_const,
            kind: expr.kind.clone(),
            value_type: expr.value_type,
            ty,
            span,
        };

        result.alloc_on(self.ir)
    }

    pub fn unary(
        &self,
        op: UnOp,
        inner: ExprP<'ir>,
        result_ty: TyP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let result = Expr::rvalue(ExprKind::Unary(op, inner), result_ty, span);

        result.alloc_on(self.ir)
    }

    pub fn r#ref(&self, inner: ExprP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        assert!(matches!(inner.value_type, ValueType::LValue));

        // optimize away deref followed by ref
        match inner.kind {
            ExprKind::Deref(inner) => return inner,
            _ => {}
        };

        let result = Expr::rvalue(
            ExprKind::Ref(inner),
            self.ir.intern_type(Ty::Pointer(inner.ty, inner.is_const)),
            span,
        );

        result.alloc_on(self.ir)
    }

    pub fn index(&self, inner: ExprP<'ir>, index: ExprP<'ir>, span: Option<Span>) -> ExprP<'ir> {
        let kind = ExprKind::Index(inner, index);
        let result = match inner.ty {
            Ty::Array(ty, _) if !inner.is_const => Expr::lvalue(kind, ty, span),
            Ty::Array(ty, _) if inner.is_const => Expr::const_lvalue(kind, ty, span),
            _ => panic!("cannot index {:?}", inner.ty),
        };

        result.alloc_on(self.ir)
    }

    pub fn const_index(&self, inner: ExprP<'ir>, index: usize, span: Option<Span>) -> ExprP<'ir> {
        let index = self.literal(
            Value::USize(index),
            self.ir.intern_type(Ty::Builtin(BuiltinType::USize)),
            span,
        );

        self.index(inner, index, span)
    }

    pub fn field(
        &self,
        obj: ExprP<'ir>,
        field_id: Id,
        ty: TyP<'ir>,
        span: Option<Span>,
    ) -> ExprP<'ir> {
        let expr = Expr {
            kind: ExprKind::Field(obj, field_id),
            value_type: obj.value_type,
            is_const: obj.is_const,
            ty,
            span,
        };

        expr.alloc_on(self.ir)
    }
}

#[derive(Clone)]
pub struct TypeBuilder<'ir> {
    ir: &'ir IrCtx<'ir>,
}

impl<'ir> TypeBuilder<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self { ir }
    }

    pub fn void(&self) -> TyP<'ir> {
        self.ir.intern_type(Ty::void())
    }

    pub fn builtin(&self, builtin: BuiltinType) -> TyP<'ir> {
        self.ir.intern_type(Ty::Builtin(builtin))
    }

    pub fn pointer(&self, inner: TyP<'ir>, is_const: bool) -> TyP<'ir> {
        self.ir.intern_type(Ty::Pointer(inner, is_const))
    }

    pub fn array(&self, inner: TyP<'ir>, size: usize) -> TyP<'ir> {
        self.ir.intern_type(Ty::Array(inner, size))
    }

    pub fn named(&self, item: ItemP<'ir>) -> TyP<'ir> {
        self.ir.intern_type(Ty::Item(item))
    }

    pub fn function<I>(&self, args: I, ret: TyP<'ir>) -> TyP<'ir>
    where
        I: IntoIterator<Item = TyP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        self.ir.intern_type(Ty::FunctionPointer(
            self.ir.arena.alloc_slice_fill_iter(args),
            ret,
        ))
    }

    pub fn tuple<I>(&self, args: I) -> TyP<'ir>
    where
        I: IntoIterator<Item = TyP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        self.ir
            .intern_type(Ty::Tuple(self.ir.arena.alloc_slice_fill_iter(args)))
    }
}
