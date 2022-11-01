use crate::common::{AluminaError, CodeErrorBuilder, HashSet};
use crate::intrinsics::CodegenIntrinsicKind;
use crate::ir::const_eval::Value;
use crate::ir::ExpressionVisitor;
use crate::ir::{IRItem, IRItemP, Statement, Ty, TyP};

use super::{default_visit_expr, ExprP};

pub struct DeadCodeEliminator<'ir> {
    alive: HashSet<IRItemP<'ir>>,
}

impl<'ir> DeadCodeEliminator<'ir> {
    pub fn new() -> Self {
        DeadCodeEliminator {
            alive: HashSet::default(),
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
            Ty::Item(i) => {
                self.visit_item(i)?;
            }
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
                for f in c.data.fields {
                    self.visit_typ(f.ty)?;
                }
                c.function.get().map(|i| self.visit_item(i)).transpose()?;
            }

            IRItem::Const(c) => {
                self.visit_typ(c.typ)?;
                self.visit_expr(
                    c.init
                        .expect("inlined consts should never appear in the IR"),
                )?;
            }

            // Should be inlined
            IRItem::Alias(_) => unreachable!(),
            IRItem::Protocol(_) => unreachable!(),
        }

        Ok(())
    }

    pub fn alive_items(&self) -> &HashSet<IRItemP<'ir>> {
        &self.alive
    }
}

impl<'ir> ExpressionVisitor<'ir> for DeadCodeEliminator<'ir> {
    fn visit_expr(&mut self, expr: ExprP<'ir>) -> Result<(), AluminaError> {
        self.visit_typ(expr.ty)?;
        default_visit_expr(self, expr)
    }

    fn visit_static(&mut self, item: IRItemP<'ir>) -> Result<(), AluminaError> {
        self.visit_item(item)
    }

    fn visit_const(&mut self, item: IRItemP<'ir>) -> Result<(), AluminaError> {
        self.visit_item(item)
    }

    fn visit_fn(&mut self, item: IRItemP<'ir>) -> Result<(), AluminaError> {
        self.visit_item(item)
    }

    fn visit_codegen_intrinsic(
        &mut self,
        kind: &CodegenIntrinsicKind<'ir>,
    ) -> Result<(), AluminaError> {
        match kind {
            CodegenIntrinsicKind::SizeOfLike(_, typ) => self.visit_typ(typ),
            _ => Ok(()),
        }
    }

    fn visit_literal(&mut self, value: &Value<'ir>) -> Result<(), AluminaError> {
        match value {
            Value::FunctionPointer(item) => self.visit_item(item),
            _ => Ok(()),
        }
    }
}
