use crate::common::{AluminaError, ArenaAllocatable, CodeErrorBuilder, HashMap};
use crate::ir::const_eval::{LValue, MallocBag, Value};
use crate::ir::{Const, Id, IrCtx, Item, ItemP};

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
            LValue::Const(inner) => Ok(LValue::Const(inner)),
            LValue::Variable(_) => unreachable!(),
        }
    }
}
