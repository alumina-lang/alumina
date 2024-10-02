use crate::common::{AluminaError, CodeDiagnostic, HashMap};
use crate::diagnostics::DiagnosticsStack;
use crate::ir::builder::ExpressionBuilder;
use crate::ir::{ExprKind, ExprP, Id, IrCtx, Statement};

use super::fold::{Folder, IdUsageCounter};
use super::LocalDef;

/// Inlining in IR is very experimental and very unstable. Basically, don't do it
/// unless you are std. The main reason this even exists is to allow some lang functions
/// that only construct a struct to be used in const contexts (looking at you slice_new!).
pub struct IrInliner;

impl IrInliner {
    pub fn inline<'ir, I>(
        diag: DiagnosticsStack,
        ir: &'ir IrCtx<'ir>,
        body: ExprP<'ir>,
        args: I,
    ) -> Result<(ExprP<'ir>, Vec<LocalDef<'ir>>), AluminaError>
    where
        I: IntoIterator<Item = (Id, ExprP<'ir>)>,
    {
        let local_counts = IdUsageCounter::count_locals(body)?;
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

        let body = Folder::fold(
            body,
            ir,
            |expr| match expr.kind {
                ExprKind::Local(id) => Ok(Some(replacements.get(&id).copied().unwrap_or(expr))),
                ExprKind::Return(_) => Err(diag.err(CodeDiagnostic::IrInlineEarlyReturn)),
                ExprKind::Goto(_) => Err(diag.err(CodeDiagnostic::IrInlineFlowControl)),
                _ => Ok(None),
            },
            |stmt| match stmt {
                Statement::Label(_) => Err(diag.err(CodeDiagnostic::IrInlineFlowControl)),
                _ => Ok(None),
            },
        )?;

        Ok((builder.block(statements, body, body.span), local_defs))
    }
}
