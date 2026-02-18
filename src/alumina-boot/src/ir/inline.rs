use crate::common::{AluminaError, HashMap};
use crate::ir::builder::ExpressionBuilder;
use crate::ir::{ExprKind, ExprP, ExpressionVisitor, Id, IrCtx, Statement, TyP};

use super::fold::{Folder, IdUsageCounter};
use super::LocalDef;

struct HasReturn(bool);

impl<'ir> ExpressionVisitor<'ir> for HasReturn {
    fn visit_return(&mut self, _expr: ExprP<'ir>) -> Result<(), AluminaError> {
        self.0 = true;
        Ok(())
    }
}

pub struct IrInliner;

impl IrInliner {
    pub fn inline<'ir, I>(
        ir: &'ir IrCtx<'ir>,
        body: ExprP<'ir>,
        callee_local_defs: &[LocalDef<'ir>],
        return_ty: TyP<'ir>,
        args: I,
    ) -> Result<(ExprP<'ir>, Vec<LocalDef<'ir>>), AluminaError>
    where
        I: IntoIterator<Item = (Id, ExprP<'ir>)>,
    {
        let local_counts = IdUsageCounter::count_locals(body)?;
        let label_ids = IdUsageCounter::count_labels(body)?;
        let builder = ExpressionBuilder::new(ir);

        let mut has_return = HasReturn(false);
        has_return.visit_expr(body)?;
        let needs_return_local = has_return.0;

        let mut statements = Vec::new();
        let mut local_defs = Vec::new();

        // Build ID remapping table for all callee locals and labels
        let mut id_remap: HashMap<Id, Id> = HashMap::default();
        for local_def in callee_local_defs {
            let new_id = ir.make_id();
            id_remap.insert(local_def.id, new_id);
            local_defs.push(LocalDef {
                id: new_id,
                ty: local_def.ty,
            });
        }
        for &label_id in label_ids.keys() {
            let new_id = ir.make_id();
            id_remap.insert(label_id, new_id);
        }

        // Bind parameters: if used more than once, create a temp local
        let mut replacements: HashMap<_, _> = args.into_iter().collect();
        for (id, expr) in replacements.iter_mut() {
            if local_counts.get(id).copied().unwrap_or(0) > 1 {
                let new_id = ir.make_id();
                let ty = expr.ty;

                let orig_expr = std::mem::replace(expr, builder.local(new_id, ty, expr.span));

                statements.push(Statement::Expression(builder.assign(
                    builder.local(new_id, ty, orig_expr.span),
                    orig_expr,
                    orig_expr.span,
                )));
                local_defs.push(LocalDef { id: new_id, ty });
            }
        }

        // Phase 1: Remap locals (non-parameter), labels, gotos, and substitute parameters
        let folded = Folder::fold(
            body,
            ir,
            |expr| match expr.kind {
                ExprKind::Local(id) => {
                    if let Some(&replacement) = replacements.get(&id) {
                        Ok(Some(replacement))
                    } else if let Some(&new_id) = id_remap.get(&id) {
                        Ok(Some(builder.local(new_id, expr.ty, expr.span)))
                    } else {
                        Ok(None)
                    }
                }
                ExprKind::Goto(id) => {
                    if let Some(&new_id) = id_remap.get(&id) {
                        Ok(Some(builder.goto(new_id, expr.span)))
                    } else {
                        Ok(None)
                    }
                }
                _ => Ok(None),
            },
            |stmt| match stmt {
                Statement::Label(id) => {
                    if let Some(&new_id) = id_remap.get(id) {
                        Ok(Some(Statement::Label(new_id)))
                    } else {
                        Ok(None)
                    }
                }
                _ => Ok(None),
            },
        )?;

        if needs_return_local {
            // Create return local and return label for functions with early returns
            let ret_local = ir.make_id();
            let ret_label = ir.make_id();
            local_defs.push(LocalDef {
                id: ret_local,
                ty: return_ty,
            });

            // Phase 2: Transform Return(inner) -> Assign(ret_local, inner) + Goto(ret_label)
            let folded = Folder::fold(
                folded,
                ir,
                |expr| match expr.kind {
                    ExprKind::Return(inner) => Ok(Some(builder.block(
                        [Statement::Expression(builder.assign(
                            builder.local(ret_local, return_ty, expr.span),
                            inner,
                            expr.span,
                        ))],
                        builder.goto(ret_label, expr.span),
                        expr.span,
                    ))),
                    _ => Ok(None),
                },
                |_stmt| Ok(None),
            )?;

            // Assign the body result to ret_local. If the body diverges (e.g. all paths
            // return early via goto), this assignment is unreachable and harmless.
            statements.push(Statement::Expression(builder.assign(
                builder.local(ret_local, return_ty, body.span),
                folded,
                body.span,
            )));
            statements.push(Statement::Label(ret_label));

            Ok((
                builder.block(
                    statements,
                    builder.local(ret_local, return_ty, body.span),
                    body.span,
                ),
                local_defs,
            ))
        } else {
            // Simple case: no returns, just use the folded body directly
            Ok((builder.block(statements, folded, body.span), local_defs))
        }
    }
}
