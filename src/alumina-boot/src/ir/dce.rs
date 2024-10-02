use crate::common::{AluminaError, CodeErrorBuilder, HashSet};
use crate::ir::const_eval::Value;
use crate::ir::ExpressionVisitor;
use crate::ir::{Item, ItemP, Ty, TyP};

use super::const_eval::LValue;
use super::{default_visit_expr, ExprP, IntrinsicValueKind};

pub struct DeadCodeEliminator<'ir> {
    alive: HashSet<ItemP<'ir>>,
}

impl<'ir> DeadCodeEliminator<'ir> {
    pub fn new() -> Self {
        DeadCodeEliminator {
            alive: HashSet::default(),
        }
    }

    fn visit_ty(&mut self, ty: TyP<'ir>) -> Result<(), AluminaError> {
        match ty {
            Ty::Builtin(_) => {}
            Ty::Pointer(t, _) => {
                self.visit_ty(t)?;
            }
            Ty::Array(t, _) => {
                self.visit_ty(t)?;
            }
            Ty::Tuple(ts) => {
                for t in ts.iter() {
                    self.visit_ty(t)?;
                }
            }
            Ty::FunctionPointer(args, ret) => {
                for arg in args.iter() {
                    self.visit_ty(arg)?;
                }
                self.visit_ty(ret)?;
            }
            Ty::Item(i) => {
                self.visit_item(i)?;
            }
        }

        Ok(())
    }

    pub fn visit_item(&mut self, item: ItemP<'ir>) -> Result<(), AluminaError> {
        match item.get().with_no_span()? {
            Item::Static(s) => {
                if s.ty.is_zero_sized() {
                    return Ok(());
                }
            }
            Item::Const(c) => {
                if c.ty.is_zero_sized() {
                    return Ok(());
                }
            }
            _ => {}
        };

        if !self.alive.insert(item) {
            return Ok(());
        }

        match item.get().with_no_span()? {
            Item::StructLike(s) => {
                for f in s.fields {
                    self.visit_ty(f.ty)?;
                }
            }
            Item::Function(f) => {
                for p in f.args {
                    self.visit_ty(p.ty)?;
                }
                self.visit_ty(f.return_type)?;
                f.body
                    .get()
                    .map(|b| {
                        for d in b.local_defs {
                            self.visit_ty(d.ty)?;
                        }

                        self.visit_expr(b.expr)?;

                        Ok::<_, AluminaError>(())
                    })
                    .transpose()?;
            }
            Item::Enum(e) => {
                self.visit_ty(e.underlying_ty)?;
                for v in e.members {
                    self.visit_expr(v.value)?;
                }
            }
            Item::Static(s) => {
                self.visit_ty(s.ty)?;
                s.init.map(|v| self.visit_expr(v)).transpose()?;
            }
            Item::Closure(c) => {
                for f in c.data.fields {
                    self.visit_ty(f.ty)?;
                }
                c.function.get().map(|i| self.visit_item(i)).transpose()?;
            }

            Item::Const(c) => {
                self.visit_ty(c.ty)?;
                self.visit_expr(c.init)?;
            }

            // Should be inlined
            Item::Alias(_) => unreachable!(),
            Item::Protocol(_) => {}
        }

        Ok(())
    }

    fn visit_lvalue(&mut self, lvalue: &LValue<'ir>) -> Result<(), AluminaError> {
        match lvalue {
            LValue::Const(item) => self.visit_item(item),
            LValue::Variable(_) => unreachable!(),
            LValue::Alloc(_) => unreachable!(),
            LValue::Field(inner, _) => self.visit_lvalue(inner),
            LValue::Index(inner, _) => self.visit_lvalue(inner),
            LValue::TupleIndex(inner, _) => self.visit_lvalue(inner),
        }
    }

    pub fn alive_items(&self) -> &HashSet<ItemP<'ir>> {
        &self.alive
    }
}

impl<'ir> ExpressionVisitor<'ir> for DeadCodeEliminator<'ir> {
    fn visit_expr(&mut self, expr: ExprP<'ir>) -> Result<(), AluminaError> {
        self.visit_ty(expr.ty)?;
        default_visit_expr(self, expr)
    }

    fn visit_item(&mut self, item: ItemP<'ir>) -> Result<(), AluminaError> {
        self.visit_item(item)
    }

    fn visit_codegen_intrinsic(
        &mut self,
        kind: &IntrinsicValueKind<'ir>,
    ) -> Result<(), AluminaError> {
        match kind {
            IntrinsicValueKind::SizeOfLike(_, ty) | IntrinsicValueKind::Dangling(ty) => {
                self.visit_ty(ty)
            }
            IntrinsicValueKind::FunctionLike(_)
            | IntrinsicValueKind::ConstLike(_)
            | IntrinsicValueKind::InConstContext
            | IntrinsicValueKind::Uninitialized
            | IntrinsicValueKind::Asm(_) => Ok(()),
            IntrinsicValueKind::Transmute(inner)
            | IntrinsicValueKind::Volatile(inner)
            | IntrinsicValueKind::Expect(inner, _) => self.visit_expr(inner),
            // These should be unreachable
            IntrinsicValueKind::ConstPanic(_)
            | IntrinsicValueKind::ConstWrite(_, _)
            | IntrinsicValueKind::ConstAlloc(_, _)
            | IntrinsicValueKind::StopIteration
            | IntrinsicValueKind::ConstFree(_) => Ok(()),
        }
    }

    fn visit_if(
        &mut self,
        cond: ExprP<'ir>,
        then: ExprP<'ir>,
        els: ExprP<'ir>,
        const_cond: Option<bool>,
    ) -> Result<(), AluminaError> {
        match const_cond {
            Some(true) => self.visit_expr(then),
            Some(false) => self.visit_expr(els),
            None => {
                self.visit_expr(cond)?;
                self.visit_expr(then)?;
                self.visit_expr(els)
            }
        }
    }

    fn visit_literal(&mut self, value: &Value<'ir>) -> Result<(), AluminaError> {
        match value {
            Value::FunctionPointer(item) => self.visit_item(item),
            Value::Array(values) => {
                for v in *values {
                    self.visit_literal(v)?;
                }
                Ok(())
            }
            Value::Struct(fields) => {
                for (_, value) in *fields {
                    self.visit_literal(value)?;
                }
                Ok(())
            }
            Value::Tuple(elems) => {
                for e in *elems {
                    self.visit_literal(e)?;
                }
                Ok(())
            }
            Value::Pointer(lvalue, _) => self.visit_lvalue(lvalue),
            _ => Ok(()),
        }
    }
}
