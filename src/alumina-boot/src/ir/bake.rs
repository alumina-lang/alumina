use crate::common::{AluminaError, ArenaAllocatable, CodeErrorBuilder, HashMap};
use crate::ir::const_eval::{LValue, MallocBag, Value};
use crate::ir::{Const, ExprP, Id, IrCtx, Item, ItemP};
use once_cell::unsync::OnceCell;

use std::cell::RefCell;

/// Bakes const-time allocations into static const items.
pub struct ConstBaker<'ir> {
    ir: &'ir IrCtx<'ir>,
    alloc_to_item: RefCell<HashMap<Id, ItemP<'ir>>>,
    malloc_bag: MallocBag<'ir>,
}

impl<'ir> ConstBaker<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>, malloc_bag: MallocBag<'ir>) -> Self {
        Self {
            ir,
            alloc_to_item: RefCell::new(HashMap::default()),
            malloc_bag,
        }
    }

    pub fn bake_item(&self, item: ItemP<'ir>) -> Result<ItemP<'ir>, AluminaError> {
        let new_item_cell = self.ir.make_item();

        let new_item = match item.get().with_no_span()? {
            Item::Const(c) => {
                let new_value = self.bake_value(c.value)?;
                let new_init = self.bake_expr(c.init)?;
                Item::Const(Const {
                    name: c.name,
                    ty: c.ty,
                    value: new_value,
                    init: new_init,
                    attributes: c.attributes,
                    span: c.span,
                })
            }
            Item::Static(s) => {
                let new_init = s.init.map(|e| self.bake_expr(e)).transpose()?;
                Item::Static(crate::ir::Static {
                    name: s.name,
                    ty: s.ty,
                    init: new_init,
                    r#extern: s.r#extern,
                    attributes: s.attributes,
                    span: s.span,
                })
            }
            Item::Function(f) => {
                let body_cell = OnceCell::new();
                if let Some(b) = f.body.get() {
                    body_cell
                        .set(crate::ir::FuncBody {
                            local_defs: b.local_defs,
                            expr: self.bake_expr(b.expr)?,
                        })
                        .ok();
                }

                Item::Function(crate::ir::Function {
                    name: f.name,
                    args: f.args,
                    return_type: f.return_type,
                    body: body_cell,
                    varargs: f.varargs,
                    attributes: f.attributes,
                    span: f.span,
                })
            }
            Item::Enum(e) => {
                let new_members: Vec<_> = e
                    .members
                    .iter()
                    .map(|m| {
                        Ok(crate::ir::EnumMember {
                            id: m.id,
                            name: m.name,
                            value: self.bake_expr(m.value)?,
                        })
                    })
                    .collect::<Result<_, AluminaError>>()?;

                Item::Enum(crate::ir::Enum {
                    name: e.name,
                    underlying_ty: e.underlying_ty,
                    members: new_members.alloc_on(self.ir),
                    attributes: e.attributes,
                    span: e.span,
                })
            }
            _ => return Ok(item),
        };

        new_item_cell.assign(new_item);
        Ok(new_item_cell)
    }

    pub fn bake_expr(&self, expr: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        use crate::ir::{Expr, ExprKind};

        let new_kind = match &expr.kind {
            ExprKind::Lit(value) => ExprKind::Lit(self.bake_value(*value)?),
            ExprKind::Local(_)
            | ExprKind::Item(_)
            | ExprKind::Unreachable
            | ExprKind::Nop
            | ExprKind::Goto(_) => return Ok(expr),
            ExprKind::Unary(op, inner) => ExprKind::Unary(*op, self.bake_expr(inner)?),
            ExprKind::Binary(op, lhs, rhs) => {
                ExprKind::Binary(*op, self.bake_expr(lhs)?, self.bake_expr(rhs)?)
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                ExprKind::AssignOp(*op, self.bake_expr(lhs)?, self.bake_expr(rhs)?)
            }
            ExprKind::Assign(lhs, rhs) => {
                ExprKind::Assign(self.bake_expr(lhs)?, self.bake_expr(rhs)?)
            }
            ExprKind::Call(callee, args) => {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|a| self.bake_expr(a))
                    .collect::<Result<_, _>>()?;
                ExprKind::Call(self.bake_expr(callee)?, new_args.alloc_on(self.ir))
            }
            ExprKind::Tuple(inits) => {
                let new_inits: Vec<_> = inits
                    .iter()
                    .map(|init| {
                        Ok(crate::ir::TupleInit {
                            index: init.index,
                            value: self.bake_expr(init.value)?,
                        })
                    })
                    .collect::<Result<_, AluminaError>>()?;
                ExprKind::Tuple(new_inits.alloc_on(self.ir))
            }
            ExprKind::Array(exprs) => {
                let new_exprs: Vec<_> = exprs
                    .iter()
                    .map(|e| self.bake_expr(e))
                    .collect::<Result<_, _>>()?;
                ExprKind::Array(new_exprs.alloc_on(self.ir))
            }
            ExprKind::Struct(inits) => {
                let new_inits: Vec<_> = inits
                    .iter()
                    .map(|init| {
                        Ok(crate::ir::StructInit {
                            field: init.field,
                            value: self.bake_expr(init.value)?,
                        })
                    })
                    .collect::<Result<_, AluminaError>>()?;
                ExprKind::Struct(new_inits.alloc_on(self.ir))
            }
            ExprKind::Index(arr, idx) => {
                ExprKind::Index(self.bake_expr(arr)?, self.bake_expr(idx)?)
            }
            ExprKind::Field(obj, field) => ExprKind::Field(self.bake_expr(obj)?, *field),
            ExprKind::TupleIndex(tup, idx) => ExprKind::TupleIndex(self.bake_expr(tup)?, *idx),
            ExprKind::Deref(inner) => ExprKind::Deref(self.bake_expr(inner)?),
            ExprKind::Ref(inner) => ExprKind::Ref(self.bake_expr(inner)?),
            ExprKind::Cast(inner) => ExprKind::Cast(self.bake_expr(inner)?),
            ExprKind::Tag(tag, inner) => ExprKind::Tag(tag, self.bake_expr(inner)?),
            ExprKind::If(cond, then_expr, else_expr, const_cond) => ExprKind::If(
                self.bake_expr(cond)?,
                self.bake_expr(then_expr)?,
                self.bake_expr(else_expr)?,
                *const_cond,
            ),
            ExprKind::Block(statements, ret) => {
                let new_statements: Vec<_> = statements
                    .iter()
                    .map(|s| match s {
                        crate::ir::Statement::Expression(e) => {
                            Ok(crate::ir::Statement::Expression(self.bake_expr(e)?))
                        }
                        crate::ir::Statement::Label(id) => Ok(crate::ir::Statement::Label(*id)),
                    })
                    .collect::<Result<_, AluminaError>>()?;
                ExprKind::Block(new_statements.alloc_on(self.ir), self.bake_expr(ret)?)
            }
            ExprKind::Return(val) => ExprKind::Return(self.bake_expr(val)?),
            ExprKind::Intrinsic(kind) => ExprKind::Intrinsic(self.bake_intrinsic(kind)?),
        };

        Ok(Expr {
            kind: new_kind,
            ty: expr.ty,
            value_type: expr.value_type,
            is_const: expr.is_const,
            span: expr.span,
        }
        .alloc_on(self.ir))
    }

    fn bake_intrinsic(
        &self,
        kind: &crate::ir::IntrinsicValueKind<'ir>,
    ) -> Result<crate::ir::IntrinsicValueKind<'ir>, AluminaError> {
        use crate::ir::IntrinsicValueKind;

        Ok(match kind {
            IntrinsicValueKind::Transmute(inner) => {
                IntrinsicValueKind::Transmute(self.bake_expr(inner)?)
            }
            IntrinsicValueKind::Volatile(inner) => {
                IntrinsicValueKind::Volatile(self.bake_expr(inner)?)
            }
            IntrinsicValueKind::Expect(inner, val) => {
                IntrinsicValueKind::Expect(self.bake_expr(inner)?, *val)
            }
            _ => kind.clone(),
        })
    }

    pub fn bake_value(&self, value: Value<'ir>) -> Result<Value<'ir>, AluminaError> {
        match value {
            Value::Pointer(lvalue, ty) => Ok(Value::Pointer(self.bake_lvalue(lvalue)?, ty)),
            Value::LValue(lvalue) => Ok(Value::LValue(self.bake_lvalue(lvalue)?)),
            Value::Tuple(values) => {
                let new_values: Vec<_> = values
                    .iter()
                    .map(|v| self.bake_value(*v))
                    .collect::<Result<_, _>>()?;
                Ok(Value::Tuple(new_values.alloc_on(self.ir)))
            }
            Value::Struct(fields) => {
                let new_fields: Vec<_> = fields
                    .iter()
                    .map(|(id, v)| Ok((*id, self.bake_value(*v)?)))
                    .collect::<Result<_, AluminaError>>()?;
                Ok(Value::Struct(
                    self.ir.arena.alloc_slice_fill_iter(new_fields),
                ))
            }
            Value::Array(values) => {
                let new_values: Vec<_> = values
                    .iter()
                    .map(|v| self.bake_value(*v))
                    .collect::<Result<_, _>>()?;
                Ok(Value::Array(new_values.alloc_on(self.ir)))
            }
            _ => Ok(value),
        }
    }

    fn bake_lvalue(&self, lvalue: LValue<'ir>) -> Result<LValue<'ir>, AluminaError> {
        match lvalue {
            LValue::Alloc(id) => {
                if let Some(&item) = self.alloc_to_item.borrow().get(&id) {
                    return Ok(LValue::Const(item));
                }

                let (value, ty) = self
                    .malloc_bag
                    .get(id)
                    .ok_or_else(|| {
                        crate::common::CodeDiagnostic::InternalError(
                            format!("allocation {:?} not found in malloc_bag", id),
                            std::backtrace::Backtrace::capture().into(),
                        )
                    })
                    .with_no_span()?;

                let baked_value = self.bake_value(value)?;

                let name = format!("__const_alloc_{:?}", id);
                let item_cell = self.ir.make_item();

                item_cell.assign(Item::Const(Const {
                    name: Some(name.alloc_on(self.ir)),
                    ty,
                    value: baked_value,
                    init: crate::ir::Expr {
                        kind: crate::ir::ExprKind::Lit(baked_value),
                        ty,
                        value_type: crate::ir::ValueType::RValue,
                        is_const: true,
                        span: None,
                    }
                    .alloc_on(self.ir),
                    attributes: &[],
                    span: None,
                }));

                self.alloc_to_item.borrow_mut().insert(id, item_cell);

                Ok(LValue::Const(item_cell))
            }
            LValue::Field(inner, field) => Ok(LValue::Field(
                self.bake_lvalue(*inner)?.alloc_on(self.ir),
                field,
            )),
            LValue::Index(inner, idx) => Ok(LValue::Index(
                self.bake_lvalue(*inner)?.alloc_on(self.ir),
                idx,
            )),
            LValue::TupleIndex(inner, idx) => Ok(LValue::TupleIndex(
                self.bake_lvalue(*inner)?.alloc_on(self.ir),
                idx,
            )),
            LValue::Const(inner) => {
                let new_inner = self.bake_item(inner)?;
                Ok(LValue::Const(new_inner))
            }
            LValue::Variable(_) => unreachable!(),
        }
    }
}
