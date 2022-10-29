use std::{cell::RefCell, collections::HashMap};

use crate::common::{ice, AluminaError, CodeErrorBuilder, CodeErrorKind};

use super::{
    builder::{ExpressionBuilder, TypeBuilder},
    ExprKind, ExprP, FuncBody, IrCtx, IrId, Statement,
};

/// Inlining in IR is very experimental and very unstable. Basically, don't do it
/// unless you are std. The main reason this even exists is to allow some lang functions
/// that only construct a struct to be used in const contexts (looking at you slice_new!).
pub struct IrInliner<'ir> {
    exprs: ExpressionBuilder<'ir>,
    types: TypeBuilder<'ir>,
    replacements: RefCell<HashMap<IrId, Option<ExprP<'ir>>>>,
}

impl<'ir> IrInliner<'ir> {
    pub fn with_replacements<I>(ir: &'ir IrCtx<'ir>, replacements: I) -> Self
    where
        I: IntoIterator<Item = (IrId, ExprP<'ir>)>,
    {
        Self {
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            replacements: RefCell::new(
                replacements
                    .into_iter()
                    .map(|(i, e)| (i, Some(e)))
                    .collect(),
            ),
        }
    }

    pub fn inline(&self, func: &FuncBody<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        if !func.local_defs.is_empty() {
            return Err(CodeErrorKind::IrInlineLocalDefs).with_no_span();
        }

        let mut statements = Vec::new();
        let mut ret = None;

        for stmt in func.statements {
            match stmt {
                Statement::Expression(e) => {
                    match e.kind {
                        ExprKind::Return(e) => {
                            if ret.replace(self.visit_expr(e)?).is_some() {
                                ice!("multiple returns in single block, this should have been optimized")
                            }
                        }
                        _ => statements.push(Statement::Expression(self.visit_expr(e)?)),
                    }
                }
                Statement::Label(_) => {
                    return Err(CodeErrorKind::IrInlineFlowControl).with_no_span()
                }
            }
        }

        Ok(self.exprs.block(
            statements,
            ret.unwrap_or_else(|| self.exprs.void(self.types.void(), super::ValueType::RValue)),
        ))
    }

    fn visit_statement(&self, stmt: &Statement<'ir>) -> Result<Statement<'ir>, AluminaError> {
        match stmt {
            Statement::Expression(e) => Ok(Statement::Expression(self.visit_expr(e)?)),
            Statement::Label(_) => Err(CodeErrorKind::IrInlineFlowControl).with_no_span(),
        }
    }

    fn visit_expr(&self, expr: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let ret = match expr.kind {
            ExprKind::Block(stmts, ret) => self.exprs.block(
                stmts
                    .iter()
                    .map(|s| self.visit_statement(s))
                    .collect::<Result<Vec<_>, _>>()?,
                self.visit_expr(ret)?,
            ),
            ExprKind::Binary(op, a, b) => {
                self.exprs
                    .binary(op, self.visit_expr(a)?, self.visit_expr(b)?, expr.ty)
            }
            ExprKind::AssignOp(op, a, b) => {
                self.exprs
                    .assign_op(op, self.visit_expr(a)?, self.visit_expr(b)?)
            }
            ExprKind::Call(callee, args) => self.exprs.call(
                self.visit_expr(callee)?,
                args.iter()
                    .map(|a| self.visit_expr(*a))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
            ),
            ExprKind::Fn(_) => expr,
            ExprKind::Static(_) => expr,
            ExprKind::Const(_) => expr,
            ExprKind::Lit(_) => expr,
            ExprKind::ConstValue(_) => expr,
            ExprKind::Unreachable => expr,
            ExprKind::Void => expr,
            ExprKind::CodegenIntrinsic(_) => expr,
            ExprKind::Local(id) => {
                if let Some(replacement) = self.replacements.borrow_mut().get_mut(&id) {
                    if let Some(replacement) = replacement.take() {
                        replacement
                    } else {
                        return Err(CodeErrorKind::IrInlineParameterReused).with_no_span();
                    }
                } else {
                    expr
                }
            }
            ExprKind::Ref(e) => self.exprs.r#ref(self.visit_expr(e)?),
            ExprKind::Deref(e) => self.exprs.deref(self.visit_expr(e)?),
            ExprKind::Return(_) => return Err(CodeErrorKind::IrInlineEarlyReturn).with_no_span(),
            ExprKind::Goto(_) => return Err(CodeErrorKind::IrInlineFlowControl).with_no_span(),
            ExprKind::Unary(op, e) => self.exprs.unary(op, self.visit_expr(e)?, expr.ty),
            ExprKind::Assign(a, b) => self.exprs.assign(self.visit_expr(a)?, self.visit_expr(b)?),
            ExprKind::Index(a, b) => self.exprs.index(self.visit_expr(a)?, self.visit_expr(b)?),
            ExprKind::Field(e, f) => self.exprs.field(self.visit_expr(e)?, f, expr.ty),
            ExprKind::TupleIndex(e, i) => self.exprs.tuple_index(self.visit_expr(e)?, i, expr.ty),
            ExprKind::If(cond, then, els) => self.exprs.if_then(
                self.visit_expr(cond)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
            ),
            ExprKind::Cast(inner) => self.exprs.cast(self.visit_expr(inner)?, expr.ty),
            ExprKind::Array(elems) => self.exprs.array(
                elems
                    .iter()
                    .map(|e| self.visit_expr(*e))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
            ),
            ExprKind::Tuple(elems) => self.exprs.tuple(
                elems
                    .iter()
                    .map(|e| self.visit_expr(e.value).map(|v| (e.index, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
            ),
            ExprKind::Struct(fields) => self.exprs.r#struct(
                fields
                    .iter()
                    .map(|f| self.visit_expr(f.value).map(|v| (f.field, v)))
                    .collect::<Result<Vec<_>, _>>()?,
                expr.ty,
            ),
        };

        Ok(ret)
    }
}
