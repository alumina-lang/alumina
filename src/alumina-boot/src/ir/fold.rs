use crate::common::{AluminaError, ArenaAllocatable, HashMap};

use super::{
    builder::ExpressionBuilder, Expr, ExprKind, ExprP, ExpressionVisitor, Id, IntrinsicValueKind,
    IrCtx, Statement,
};

pub struct IdUsageCounter {
    locals: HashMap<Id, usize>,
    labels: HashMap<Id, usize>,
}

impl IdUsageCounter {
    pub fn count_locals(expr: ExprP<'_>) -> Result<HashMap<Id, usize>, AluminaError> {
        let mut counter = Self {
            locals: HashMap::default(),
            labels: HashMap::default(),
        };
        counter.visit_expr(expr)?;
        Ok(counter.locals)
    }

    pub fn count_labels(expr: ExprP<'_>) -> Result<HashMap<Id, usize>, AluminaError> {
        let mut counter = Self {
            locals: HashMap::default(),
            labels: HashMap::default(),
        };
        counter.visit_expr(expr)?;
        Ok(counter.labels)
    }
}

impl<'ir> ExpressionVisitor<'ir> for IdUsageCounter {
    fn visit_local(&mut self, id: Id) -> Result<(), AluminaError> {
        *self.locals.entry(id).or_insert(0) += 1;
        Ok(())
    }

    fn visit_statement(&mut self, stmt: &Statement<'ir>) -> Result<(), AluminaError> {
        match stmt {
            Statement::Label(id) => {
                *self.labels.entry(*id).or_insert(0) += 1;
            }
            _ => {}
        }
        Ok(())
    }
}

pub struct Folder<'ir, E, S> {
    ir: &'ir IrCtx<'ir>,
    expr_func: E,
    stmt_func: S,
}

impl<'ir, E, S> Folder<'ir, E, S>
where
    E: FnMut(ExprP<'ir>) -> Result<Option<ExprP<'ir>>, AluminaError>,
    S: FnMut(&Statement<'ir>) -> Result<Option<Statement<'ir>>, AluminaError>,
{
    pub fn fold(
        expr: ExprP<'ir>,
        ir: &'ir IrCtx<'ir>,
        expr_func: E,
        stmt_func: S,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let mut folder = Self {
            ir,
            expr_func,
            stmt_func,
        };
        folder.fold_expr(expr)
    }

    fn fold_statement(&mut self, stmt: &Statement<'ir>) -> Result<Statement<'ir>, AluminaError> {
        match (self.stmt_func)(stmt) {
            Ok(Some(stmt)) => return Ok(stmt),
            Err(e) => return Err(e),
            _ => {}
        };

        let ret = match stmt {
            Statement::Expression(e) => Statement::Expression(self.fold_expr(e)?),
            Statement::Label(i) => Statement::Label(*i),
        };

        Ok(ret)
    }

    fn fold_expr(&mut self, expr: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let builder = ExpressionBuilder::new(self.ir);

        match (self.expr_func)(expr) {
            Ok(Some(expr)) => return Ok(expr),
            Err(e) => return Err(e),
            _ => {}
        };

        let ret = match expr.kind {
            ExprKind::Block(stmts, ret) => builder.block(
                stmts
                    .iter()
                    .map(|s| self.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?,
                self.fold_expr(ret)?,
                expr.span,
            ),
            ExprKind::Binary(op, a, b) => builder.binary(
                op,
                self.fold_expr(a)?,
                self.fold_expr(b)?,
                expr.ty,
                expr.span,
            ),
            ExprKind::AssignOp(op, a, b) => {
                builder.assign_op(op, self.fold_expr(a)?, self.fold_expr(b)?, expr.span)
            }
            ExprKind::Call(callee, args) => builder.call(
                self.fold_expr(callee)?,
                args.iter()
                    .map(|a| self.fold_expr(a))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Local(id) => builder.local(id, expr.ty, expr.span),
            ExprKind::Ref(e) => builder.r#ref(self.fold_expr(e)?, expr.span),
            ExprKind::Deref(e) => builder.deref(self.fold_expr(e)?, expr.span),
            ExprKind::Return(inner) => builder.ret(self.fold_expr(inner)?, expr.span),
            ExprKind::Goto(id) => builder.goto(id, expr.span),
            ExprKind::Unary(op, e) => builder.unary(op, self.fold_expr(e)?, expr.ty, expr.span),
            ExprKind::Assign(a, b) => {
                builder.assign(self.fold_expr(a)?, self.fold_expr(b)?, expr.span)
            }
            ExprKind::Index(a, b) => {
                builder.index(self.fold_expr(a)?, self.fold_expr(b)?, expr.span)
            }
            ExprKind::Field(e, f) => builder.field(self.fold_expr(e)?, f, expr.ty, expr.span),
            ExprKind::TupleIndex(e, i) => {
                builder.tuple_index(self.fold_expr(e)?, i, expr.ty, expr.span)
            }
            ExprKind::Tag(tag, inner) => Expr {
                kind: ExprKind::Tag(tag, self.fold_expr(inner)?),
                ty: expr.ty,
                is_const: expr.is_const,
                value_type: expr.value_type,
                span: expr.span,
            }
            .alloc_on(self.ir),
            ExprKind::If(cond, then, els, const_cond) => builder.if_then(
                self.fold_expr(cond)?,
                self.fold_expr(then)?,
                self.fold_expr(els)?,
                const_cond,
                expr.span,
            ),
            ExprKind::Cast(inner) => builder.cast(self.fold_expr(inner)?, expr.ty, expr.span),
            ExprKind::Array(elems) => builder.array(
                elems
                    .iter()
                    .map(|e| self.fold_expr(e))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Tuple(elems) => builder.tuple(
                elems
                    .iter()
                    .map(|e| self.fold_expr(e.value).map(|v| (e.index, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Struct(fields) => builder.r#struct(
                fields
                    .iter()
                    .map(|f| self.fold_expr(f.value).map(|v| (f.field, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Intrinsic(ref kind) => match kind {
                IntrinsicValueKind::ConstPanic(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstPanic(self.fold_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::ConstWrite(inner, b) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstWrite(self.fold_expr(inner)?, *b),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::ConstAlloc(ty, inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstAlloc(ty, self.fold_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::ConstFree(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstFree(self.fold_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::Transmute(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Transmute(self.fold_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::Volatile(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Volatile(self.fold_expr(inner)?),
                    expr.ty,
                    expr.span,
                ),
                IntrinsicValueKind::SizeOfLike(_, _)
                | IntrinsicValueKind::Dangling(_)
                | IntrinsicValueKind::Asm(_)
                | IntrinsicValueKind::FunctionLike(_)
                | IntrinsicValueKind::ConstLike(_)
                | IntrinsicValueKind::Uninitialized
                | IntrinsicValueKind::StopIteration
                | IntrinsicValueKind::InConstContext => Expr {
                    is_const: expr.is_const,
                    ty: expr.ty,
                    kind: expr.kind.clone(),
                    value_type: expr.value_type,
                    span: expr.span,
                }
                .alloc_on(self.ir),
                IntrinsicValueKind::Expect(inner, val) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Expect(self.fold_expr(inner)?, *val),
                    expr.ty,
                    expr.span,
                ),
            },
            ExprKind::Item(_) | ExprKind::Lit(_) | ExprKind::Unreachable | ExprKind::Nop => Expr {
                is_const: expr.is_const,
                ty: expr.ty,
                kind: expr.kind.clone(),
                value_type: expr.value_type,
                span: expr.span,
            }
            .alloc_on(self.ir),
        };

        Ok(ret)
    }
}
