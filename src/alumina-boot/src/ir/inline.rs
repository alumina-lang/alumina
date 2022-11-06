use crate::common::{AluminaError, CodeErrorBuilder, CodeErrorKind, HashMap};
use crate::ir::builder::ExpressionBuilder;
use crate::ir::{ExprKind, ExprP, IrCtx, IrId, Statement};

use super::{ExpressionVisitor, LocalDef};

struct LocalUsageCounter {
    usage: HashMap<IrId, usize>,
}

impl LocalUsageCounter {
    fn count_usages(expr: ExprP<'_>) -> Result<HashMap<IrId, usize>, AluminaError> {
        let mut counter = Self {
            usage: HashMap::default(),
        };
        counter.visit_expr(expr)?;
        Ok(counter.usage)
    }
}

impl<'ir> ExpressionVisitor<'ir> for LocalUsageCounter {
    fn visit_local(&mut self, id: IrId) -> Result<(), AluminaError> {
        *self.usage.entry(id).or_insert(0) += 1;
        Ok(())
    }
}

/// Inlining in IR is very experimental and very unstable. Basically, don't do it
/// unless you are std. The main reason this even exists is to allow some lang functions
/// that only construct a struct to be used in const contexts (looking at you slice_new!).
pub struct IrInliner<'ir> {
    ir: &'ir IrCtx<'ir>,
    replacements: HashMap<IrId, ExprP<'ir>>,
}

impl<'ir> IrInliner<'ir> {
    fn visit_statement(&mut self, stmt: &Statement<'ir>) -> Result<Statement<'ir>, AluminaError> {
        match stmt {
            Statement::Expression(e) => Ok(Statement::Expression(self.visit_expr(e)?)),
            Statement::Label(_) => Err(CodeErrorKind::IrInlineFlowControl).with_no_span(),
        }
    }

    pub fn inline<I>(
        ir: &'ir IrCtx<'ir>,
        body: ExprP<'ir>,
        args: I,
    ) -> Result<(ExprP<'ir>, Vec<LocalDef<'ir>>), AluminaError>
    where
        I: IntoIterator<Item = (IrId, ExprP<'ir>)>,
    {
        let local_counts = LocalUsageCounter::count_usages(body)?;
        let mut statements = Vec::new();
        let builder = ExpressionBuilder::new(ir);

        let mut local_defs = Vec::new();
        let mut replacements: HashMap<_, _> = args.into_iter().collect();

        for (id, expr) in replacements.iter_mut() {
            if local_counts.get(id).copied().unwrap_or(0) > 1 {
                let new_id = ir.make_id();
                let ty = expr.ty;

                let expr = std::mem::replace(expr, builder.local(new_id, ty, expr.span));

                statements.push(Statement::Expression(builder.assign(
                    builder.local(new_id, ty, expr.span),
                    expr,
                    expr.span,
                )));
                local_defs.push(LocalDef {
                    id: new_id,
                    typ: ty,
                });
            }
        }

        let mut inliner = Self { ir, replacements };

        Ok((
            builder.block(statements, inliner.visit_expr(body)?, body.span),
            local_defs,
        ))
    }

    fn visit_expr(&mut self, expr: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let builder = ExpressionBuilder::new(self.ir);

        let ret = match expr.kind {
            ExprKind::Block(stmts, ret) => builder.block(
                stmts
                    .iter()
                    .map(|s| self.visit_statement(s))
                    .collect::<Result<Vec<_>, _>>()?,
                self.visit_expr(ret)?,
                expr.span,
            ),
            ExprKind::Binary(op, a, b) => builder.binary(
                op,
                self.visit_expr(a)?,
                self.visit_expr(b)?,
                expr.ty,
                expr.span,
            ),
            ExprKind::AssignOp(op, a, b) => {
                builder.assign_op(op, self.visit_expr(a)?, self.visit_expr(b)?, expr.span)
            }
            ExprKind::Call(callee, args) => builder.call(
                self.visit_expr(callee)?,
                args.iter()
                    .map(|a| self.visit_expr(a))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Fn(_) => expr,
            ExprKind::Static(_) => expr,
            ExprKind::Const(_) => expr,
            ExprKind::Literal(_) => expr,
            ExprKind::Unreachable => expr,
            ExprKind::Void => expr,
            ExprKind::Intrinsic(_) => expr,
            ExprKind::Local(id) => self.replacements.get(&id).copied().unwrap_or(expr),
            ExprKind::Ref(e) => builder.r#ref(self.visit_expr(e)?, expr.span),
            ExprKind::Deref(e) => builder.deref(self.visit_expr(e)?, expr.span),
            ExprKind::Return(_) => return Err(CodeErrorKind::IrInlineEarlyReturn).with_no_span(),
            ExprKind::Goto(_) => return Err(CodeErrorKind::IrInlineFlowControl).with_no_span(),
            ExprKind::Unary(op, e) => builder.unary(op, self.visit_expr(e)?, expr.ty, expr.span),
            ExprKind::Assign(a, b) => {
                builder.assign(self.visit_expr(a)?, self.visit_expr(b)?, expr.span)
            }
            ExprKind::Index(a, b) => {
                builder.index(self.visit_expr(a)?, self.visit_expr(b)?, expr.span)
            }
            ExprKind::Field(e, f) => builder.field(self.visit_expr(e)?, f, expr.ty, expr.span),
            ExprKind::TupleIndex(e, i) => {
                builder.tuple_index(self.visit_expr(e)?, i, expr.ty, expr.span)
            }
            ExprKind::If(cond, then, els) => builder.if_then(
                self.visit_expr(cond)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
                expr.span,
            ),
            ExprKind::Cast(inner) => builder.cast(self.visit_expr(inner)?, expr.ty, expr.span),
            ExprKind::Array(elems) => builder.array(
                elems
                    .iter()
                    .map(|e| self.visit_expr(e))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Tuple(elems) => builder.tuple(
                elems
                    .iter()
                    .map(|e| self.visit_expr(e.value).map(|v| (e.index, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
            ExprKind::Struct(fields) => builder.r#struct(
                fields
                    .iter()
                    .map(|f| self.visit_expr(f.value).map(|v| (f.field, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                expr.span,
            ),
        };

        Ok(ret)
    }
}
