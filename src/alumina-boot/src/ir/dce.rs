use std::collections::HashSet;

use crate::common::{AluminaError, CodeErrorBuilder};

use super::{ExprKind, ExprP, IRItem, IRItemP, Statement, Ty, TyP};

pub struct DeadCodeEliminator<'ir> {
    alive: HashSet<IRItemP<'ir>>,
}

impl<'ir> DeadCodeEliminator<'ir> {
    pub fn new() -> Self {
        DeadCodeEliminator {
            alive: HashSet::new(),
        }
    }

    fn visit_typ(&mut self, typ: TyP<'ir>) -> Result<(), AluminaError> {
        match typ {
            Ty::Builtin(_) => {}

            Ty::Pointer(t, _) => {
                self.visit_typ(t)?;
            }
            Ty::Array(t, _) => {
                self.visit_typ(t)?;
            }
            Ty::Tuple(ts) => {
                for t in ts.iter() {
                    self.visit_typ(t)?;
                }
            }
            Ty::FunctionPointer(args, ret) => {
                for arg in args.iter() {
                    self.visit_typ(arg)?;
                }
                self.visit_typ(ret)?;
            }
            Ty::NamedType(i) | Ty::NamedFunction(i) | Ty::Closure(i) => {
                self.visit_item(i)?;
            }

            Ty::Protocol(_) => unreachable!(),

            Ty::Unqualified(_) => {
                // skipped, this is only for codegen
            }
        }

        Ok(())
    }

    fn visit_expr(&mut self, expr: ExprP<'ir>) -> Result<(), AluminaError> {
        self.visit_typ(expr.ty)?;

        match expr.kind {
            ExprKind::Block(stmts, ret) => {
                for s in stmts {
                    match s {
                        Statement::Expression(e) => self.visit_expr(e)?,
                        Statement::Label(_) => {}
                    }
                }
                self.visit_expr(ret)?;
            }
            ExprKind::Binary(_, lhs, rhs) => {
                self.visit_expr(lhs)?;
                self.visit_expr(rhs)?;
            }
            ExprKind::AssignOp(_, lhs, rhs) => {
                self.visit_expr(lhs)?;
                self.visit_expr(rhs)?;
            }
            ExprKind::Call(callee, args) => {
                self.visit_expr(callee)?;
                for arg in args.iter() {
                    self.visit_expr(arg)?;
                }
            }
            ExprKind::Ref(inner) => {
                self.visit_expr(inner)?;
            }
            ExprKind::Deref(inner) => {
                self.visit_expr(inner)?;
            }
            ExprKind::Return(ret) => {
                self.visit_expr(ret)?;
            }
            ExprKind::Unary(_, op) => {
                self.visit_expr(op)?;
            }
            ExprKind::Assign(lhs, rhs) => {
                self.visit_expr(lhs)?;
                self.visit_expr(rhs)?;
            }
            ExprKind::Index(indexee, index) => {
                self.visit_expr(indexee)?;
                self.visit_expr(index)?;
            }
            ExprKind::Field(s, _) => {
                self.visit_expr(s)?;
            }
            ExprKind::TupleIndex(tup, _) => {
                self.visit_expr(tup)?;
            }
            ExprKind::If(cond, then, els) => {
                self.visit_expr(cond)?;
                self.visit_expr(then)?;
                self.visit_expr(els)?;
            }
            ExprKind::Cast(inner) => {
                self.visit_expr(inner)?;
            }

            ExprKind::Fn(i) | ExprKind::Static(i) => {
                self.visit_item(i)?;
            }

            ExprKind::Local(_)
            | ExprKind::Lit(_)
            | ExprKind::ConstValue(_)
            | ExprKind::Goto(_)
            | ExprKind::CodegenIntrinsic(_)
            | ExprKind::Unreachable
            | ExprKind::Void => {}
        }

        Ok(())
    }

    pub fn visit_item(&mut self, item: IRItemP<'ir>) -> Result<(), AluminaError> {
        if !self.alive.insert(item) {
            return Ok(());
        }

        match item.get().with_no_span()? {
            IRItem::StructLike(s) => {
                for f in s.fields {
                    self.visit_typ(f.ty)?;
                }
            }
            IRItem::Function(f) => {
                for p in f.args {
                    self.visit_typ(p.ty)?;
                }
                self.visit_typ(f.return_type)?;
                f.body
                    .get()
                    .map(|b| {
                        for d in b.local_defs {
                            self.visit_typ(d.typ)?;
                        }

                        for s in b.statements {
                            match s {
                                Statement::Expression(e) => self.visit_expr(e)?,
                                Statement::Label(_) => {}
                            }
                        }

                        Ok::<_, AluminaError>(())
                    })
                    .transpose()?;
            }
            IRItem::Enum(e) => {
                self.visit_typ(e.underlying_type)?;
                for v in e.members {
                    // TODO: is this needed? It should always be a constant value
                    self.visit_expr(v.value)?;
                }
            }
            IRItem::Static(s) => {
                self.visit_typ(s.typ)?;
                s.init.map(|v| self.visit_expr(v)).transpose()?;
            }
            IRItem::Closure(c) => {
                for f in c.fields {
                    self.visit_typ(f.ty)?;
                }
                c.function.get().map(|i| self.visit_item(i)).transpose()?;
            }

            // Should be inlined
            IRItem::Const(_) => unreachable!(),
            IRItem::Alias(_) => unreachable!(),
            IRItem::Protocol(_) => unreachable!(),
        }

        Ok(())
    }

    pub fn alive_items(&self) -> &HashSet<IRItemP<'ir>> {
        &self.alive
    }
}
