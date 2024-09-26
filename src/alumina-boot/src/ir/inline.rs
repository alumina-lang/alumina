use crate::ast::Span;
use crate::common::{AluminaError, ArenaAllocatable, CodeDiagnostic, HashMap};
use crate::diagnostics::DiagnosticsStack;
use crate::intrinsics::IntrinsicValueKind;
use crate::ir::builder::ExpressionBuilder;
use crate::ir::{ExprKind, ExprP, Id, IrCtx, Statement};

use super::{Expr, ExpressionVisitor, LocalDef};

struct LocalUsageCounter {
    usage: HashMap<Id, usize>,
}

impl LocalUsageCounter {
    fn count_usages(expr: ExprP<'_>) -> Result<HashMap<Id, usize>, AluminaError> {
        let mut counter = Self {
            usage: HashMap::default(),
        };
        counter.visit_expr(expr)?;
        Ok(counter.usage)
    }
}

impl<'ir> ExpressionVisitor<'ir> for LocalUsageCounter {
    fn visit_local(&mut self, id: Id) -> Result<(), AluminaError> {
        *self.usage.entry(id).or_insert(0) += 1;
        Ok(())
    }
}

/// Inlining in IR is very experimental and very unstable. Basically, don't do it
/// unless you are std. The main reason this even exists is to allow some lang functions
/// that only construct a struct to be used in const contexts (looking at you slice_new!).
pub struct IrInliner<'ir> {
    diag: DiagnosticsStack,
    ir: &'ir IrCtx<'ir>,
    replacements: HashMap<Id, ExprP<'ir>>,
    span: Option<Span>,
}

impl<'ir> IrInliner<'ir> {
    fn visit_statement(&mut self, stmt: &Statement<'ir>) -> Result<Statement<'ir>, AluminaError> {
        match stmt {
            Statement::Expression(e) => Ok(Statement::Expression(self.visit_expr(e)?)),
            Statement::Label(_) => Err(self.diag.err(CodeDiagnostic::IrInlineFlowControl)),
        }
    }

    pub fn inline<I>(
        diag: DiagnosticsStack,
        ir: &'ir IrCtx<'ir>,
        body: ExprP<'ir>,
        args: I,
        span: Option<Span>,
    ) -> Result<(ExprP<'ir>, Vec<LocalDef<'ir>>), AluminaError>
    where
        I: IntoIterator<Item = (Id, ExprP<'ir>)>,
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
                local_defs.push(LocalDef { id: new_id, ty });
            }
        }

        let mut inliner = Self {
            diag,
            ir,
            replacements,
            span,
        };

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
                self.span,
            ),
            ExprKind::Binary(op, a, b) => builder.binary(
                op,
                self.visit_expr(a)?,
                self.visit_expr(b)?,
                expr.ty,
                self.span,
            ),
            ExprKind::AssignOp(op, a, b) => {
                builder.assign_op(op, self.visit_expr(a)?, self.visit_expr(b)?, self.span)
            }
            ExprKind::Call(callee, args) => builder.call(
                self.visit_expr(callee)?,
                args.iter()
                    .map(|a| self.visit_expr(a))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                self.span,
            ),
            ExprKind::Local(id) => self.replacements.get(&id).copied().unwrap_or(expr),
            ExprKind::Ref(e) => builder.r#ref(self.visit_expr(e)?, self.span),
            ExprKind::Deref(e) => builder.deref(self.visit_expr(e)?, self.span),
            ExprKind::Return(_) => return Err(self.diag.err(CodeDiagnostic::IrInlineEarlyReturn)),
            ExprKind::Goto(_) => return Err(self.diag.err(CodeDiagnostic::IrInlineFlowControl)),
            ExprKind::Unary(op, e) => builder.unary(op, self.visit_expr(e)?, expr.ty, self.span),
            ExprKind::Assign(a, b) => {
                builder.assign(self.visit_expr(a)?, self.visit_expr(b)?, self.span)
            }
            ExprKind::Index(a, b) => {
                builder.index(self.visit_expr(a)?, self.visit_expr(b)?, self.span)
            }
            ExprKind::Field(e, f) => builder.field(self.visit_expr(e)?, f, expr.ty, self.span),
            ExprKind::TupleIndex(e, i) => {
                builder.tuple_index(self.visit_expr(e)?, i, expr.ty, self.span)
            }
            ExprKind::Tag(tag, inner) => Expr {
                kind: ExprKind::Tag(tag, self.visit_expr(inner)?),
                ty: expr.ty,
                is_const: expr.is_const,
                value_type: expr.value_type,
                span: self.span,
            }
            .alloc_on(self.ir),
            ExprKind::If(cond, then, els, const_cond) => builder.if_then(
                self.visit_expr(cond)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
                const_cond,
                self.span,
            ),
            ExprKind::Cast(inner) => builder.cast(self.visit_expr(inner)?, expr.ty, self.span),
            ExprKind::Array(elems) => builder.array(
                elems
                    .iter()
                    .map(|e| self.visit_expr(e))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                self.span,
            ),
            ExprKind::Tuple(elems) => builder.tuple(
                elems
                    .iter()
                    .map(|e| self.visit_expr(e.value).map(|v| (e.index, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                self.span,
            ),
            ExprKind::Struct(fields) => builder.r#struct(
                fields
                    .iter()
                    .map(|f| self.visit_expr(f.value).map(|v| (f.field, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
                self.span,
            ),
            ExprKind::Intrinsic(ref kind) => match kind {
                IntrinsicValueKind::ConstPanic(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstPanic(self.visit_expr(inner)?),
                    expr.ty,
                    self.span,
                ),
                IntrinsicValueKind::ConstWrite(inner, b) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstWrite(self.visit_expr(inner)?, *b),
                    expr.ty,
                    self.span,
                ),
                IntrinsicValueKind::ConstAlloc(ty, inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstAlloc(ty, self.visit_expr(inner)?),
                    expr.ty,
                    self.span,
                ),
                IntrinsicValueKind::ConstFree(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::ConstFree(self.visit_expr(inner)?),
                    expr.ty,
                    self.span,
                ),
                IntrinsicValueKind::Transmute(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Transmute(self.visit_expr(inner)?),
                    expr.ty,
                    self.span,
                ),
                IntrinsicValueKind::Volatile(inner) => builder.codegen_intrinsic(
                    IntrinsicValueKind::Volatile(self.visit_expr(inner)?),
                    expr.ty,
                    self.span,
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
                    span: self.span,
                }
                .alloc_on(self.ir),
            },
            ExprKind::Item(_) | ExprKind::Lit(_) | ExprKind::Unreachable | ExprKind::Nop => {
                // Just replace span
                Expr {
                    is_const: expr.is_const,
                    ty: expr.ty,
                    kind: expr.kind.clone(),
                    value_type: expr.value_type,
                    span: self.span,
                }
                .alloc_on(self.ir)
            }
        };

        Ok(ret)
    }
}
