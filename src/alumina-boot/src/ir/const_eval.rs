/// Const evaluation at the moment is very rudimentary and is there only to support things like
/// the fixed-size array lengths and enum values.
use crate::ast::BinOp;
use crate::common::HashMap;
use crate::ir::{BuiltinType, ExprKind, ExprP, IrCtx, IrId, Statement, Ty, TyP, UnOp};
use std::cmp::Ordering;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Value<'ir> {
    Void,
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    USize(usize),
    ISize(isize),
    F32(&'ir str),
    F64(&'ir str),
    Str(&'ir [u8]),
    Tuple(&'ir [Value<'ir>]),
    Array(&'ir [Value<'ir>]),
    Struct(&'ir [(IrId, Value<'ir>)]),
    FunctionPointer(super::IRItemP<'ir>),
}

#[derive(Debug, Error, Clone, Hash, PartialEq, Eq)]
pub enum ConstEvalError {
    #[error("not constant or unsupported expression")]
    Unsupported,
    #[error("ice: encountered a branch in constant evaluation that should have been rejected during type checking")]
    CompilerBug,
    #[error("trying to access uninitialized field during constant evaluation")]
    UninitializedField,
    #[error("index out of bounds")]
    IndexOutOfBounds,
    #[error("arithmetic overflow")]
    ArithmeticOverflow,
    #[error("division by zero")]
    DivisionByZero,
}

type Result<T> = std::result::Result<T, ConstEvalError>;

macro_rules! numeric_of_kind {
    ($kind:expr, $val:expr) => {
        match $kind {
            BuiltinType::U8 => Value::U8($val),
            BuiltinType::U16 => Value::U16($val),
            BuiltinType::U32 => Value::U32($val),
            BuiltinType::U64 => Value::U64($val),
            BuiltinType::U128 => Value::U128($val),
            BuiltinType::I8 => Value::I8($val),
            BuiltinType::I16 => Value::I16($val),
            BuiltinType::I32 => Value::I32($val),
            BuiltinType::I64 => Value::I64($val),
            BuiltinType::I128 => Value::I128($val),
            BuiltinType::USize => Value::USize($val),
            BuiltinType::ISize => Value::ISize($val),
            _ => unreachable!(),
        }
    };
}

pub(crate) use numeric_of_kind;

impl<'ir> Value<'ir> {
    fn equal(self, other: Value) -> Result<Value<'ir>> {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
            (Value::U8(a), Value::U8(b)) => Ok(Value::Bool(a == b)),
            (Value::U16(a), Value::U16(b)) => Ok(Value::Bool(a == b)),
            (Value::U32(a), Value::U32(b)) => Ok(Value::Bool(a == b)),
            (Value::U64(a), Value::U64(b)) => Ok(Value::Bool(a == b)),
            (Value::U128(a), Value::U128(b)) => Ok(Value::Bool(a == b)),
            (Value::I8(a), Value::I8(b)) => Ok(Value::Bool(a == b)),
            (Value::I16(a), Value::I16(b)) => Ok(Value::Bool(a == b)),
            (Value::I32(a), Value::I32(b)) => Ok(Value::Bool(a == b)),
            (Value::I64(a), Value::I64(b)) => Ok(Value::Bool(a == b)),
            (Value::I128(a), Value::I128(b)) => Ok(Value::Bool(a == b)),
            (Value::USize(a), Value::USize(b)) => Ok(Value::Bool(a == b)),
            (Value::ISize(a), Value::ISize(b)) => Ok(Value::Bool(a == b)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }

    fn cmp(self, other: Value) -> Result<Ordering> {
        match (self, other) {
            (Value::U8(a), Value::U8(b)) => Ok(a.cmp(&b)),
            (Value::U16(a), Value::U16(b)) => Ok(a.cmp(&b)),
            (Value::U32(a), Value::U32(b)) => Ok(a.cmp(&b)),
            (Value::U64(a), Value::U64(b)) => Ok(a.cmp(&b)),
            (Value::U128(a), Value::U128(b)) => Ok(a.cmp(&b)),
            (Value::I8(a), Value::I8(b)) => Ok(a.cmp(&b)),
            (Value::I16(a), Value::I16(b)) => Ok(a.cmp(&b)),
            (Value::I32(a), Value::I32(b)) => Ok(a.cmp(&b)),
            (Value::I64(a), Value::I64(b)) => Ok(a.cmp(&b)),
            (Value::I128(a), Value::I128(b)) => Ok(a.cmp(&b)),
            (Value::USize(a), Value::USize(b)) => Ok(a.cmp(&b)),
            (Value::ISize(a), Value::ISize(b)) => Ok(a.cmp(&b)),
            (Value::Bool(a), Value::Bool(b)) => Ok(a.cmp(&b)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Add for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn add(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8(a.wrapping_add(b))),
            (U16(a), U16(b)) => Ok(U16(a.wrapping_add(b))),
            (U32(a), U32(b)) => Ok(U32(a.wrapping_add(b))),
            (U64(a), U64(b)) => Ok(U64(a.wrapping_add(b))),
            (U128(a), U128(b)) => Ok(U128(a.wrapping_add(b))),
            (USize(a), USize(b)) => Ok(USize(a.wrapping_add(b))),

            // Signed overflow is undefined behavior, so we reject it
            (I8(a), I8(b)) => a
                .checked_add(b)
                .map(I8)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I16(a), I16(b)) => a
                .checked_add(b)
                .map(I16)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I32(a), I32(b)) => a
                .checked_add(b)
                .map(I32)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I64(a), I64(b)) => a
                .checked_add(b)
                .map(I64)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I128(a), I128(b)) => a
                .checked_add(b)
                .map(I128)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (ISize(a), ISize(b)) => a
                .checked_add(b)
                .map(ISize)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Sub for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn sub(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8(a.wrapping_sub(b))),
            (U16(a), U16(b)) => Ok(U16(a.wrapping_sub(b))),
            (U32(a), U32(b)) => Ok(U32(a.wrapping_sub(b))),
            (U64(a), U64(b)) => Ok(U64(a.wrapping_sub(b))),
            (U128(a), U128(b)) => Ok(U128(a.wrapping_sub(b))),
            (USize(a), USize(b)) => Ok(USize(a.wrapping_sub(b))),

            // Signed overflow is undefined behavior, so we reject it
            (I8(a), I8(b)) => a
                .checked_sub(b)
                .map(I8)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I16(a), I16(b)) => a
                .checked_sub(b)
                .map(I16)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I32(a), I32(b)) => a
                .checked_sub(b)
                .map(I32)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I64(a), I64(b)) => a
                .checked_sub(b)
                .map(I64)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I128(a), I128(b)) => a
                .checked_sub(b)
                .map(I128)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (ISize(a), ISize(b)) => a
                .checked_sub(b)
                .map(ISize)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Mul for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn mul(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8(a.wrapping_mul(b))),
            (U16(a), U16(b)) => Ok(U16(a.wrapping_mul(b))),
            (U32(a), U32(b)) => Ok(U32(a.wrapping_mul(b))),
            (U64(a), U64(b)) => Ok(U64(a.wrapping_mul(b))),
            (U128(a), U128(b)) => Ok(U128(a.wrapping_mul(b))),
            (USize(a), USize(b)) => Ok(USize(a.wrapping_mul(b))),

            // Signed overflow is undefined behavior, so we reject it
            (I8(a), I8(b)) => a
                .checked_mul(b)
                .map(I8)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I16(a), I16(b)) => a
                .checked_mul(b)
                .map(I16)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I32(a), I32(b)) => a
                .checked_mul(b)
                .map(I32)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I64(a), I64(b)) => a
                .checked_mul(b)
                .map(I64)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (I128(a), I128(b)) => a
                .checked_mul(b)
                .map(I128)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            (ISize(a), ISize(b)) => a
                .checked_mul(b)
                .map(ISize)
                .ok_or(ConstEvalError::ArithmeticOverflow),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Shl<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn shl(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        let other = match other {
            USize(a) => a,
            _ => return Err(ConstEvalError::CompilerBug),
        };

        match self {
            U8(a) => Ok(U8(a << other)),
            U16(a) => Ok(U16(a << other)),
            U32(a) => Ok(U32(a << other)),
            U64(a) => Ok(U64(a << other)),
            U128(a) => Ok(U128(a << other)),
            I8(a) => Ok(I8(a << other)),
            I16(a) => Ok(I16(a << other)),
            I32(a) => Ok(I32(a << other)),
            I64(a) => Ok(I64(a << other)),
            I128(a) => Ok(I128(a << other)),
            USize(a) => Ok(USize(a << other)),
            ISize(a) => Ok(ISize(a << other)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Neg for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn neg(self) -> Result<Value<'ir>> {
        use Value::*;

        match self {
            I8(a) => Ok(I8(-a)),
            I16(a) => Ok(I16(-a)),
            I32(a) => Ok(I32(-a)),
            I64(a) => Ok(I64(-a)),
            I128(a) => Ok(I128(-a)),
            ISize(a) => Ok(ISize(-a)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Not for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn not(self) -> Result<Value<'ir>> {
        use Value::*;

        match self {
            U8(a) => Ok(U8(!a)),
            U16(a) => Ok(U16(!a)),
            U32(a) => Ok(U32(!a)),
            U64(a) => Ok(U64(!a)),
            U128(a) => Ok(U128(!a)),
            I8(a) => Ok(I8(!a)),
            I16(a) => Ok(I16(!a)),
            I32(a) => Ok(I32(!a)),
            I64(a) => Ok(I64(!a)),
            I128(a) => Ok(I128(!a)),
            USize(a) => Ok(USize(!a)),
            ISize(a) => Ok(ISize(!a)),
            Bool(a) => Ok(Bool(!a)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Shr<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn shr(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        let other = match other {
            USize(a) => a,
            _ => return Err(ConstEvalError::CompilerBug),
        };

        match self {
            U8(a) => Ok(U8(a >> other)),
            U16(a) => Ok(U16(a >> other)),
            U32(a) => Ok(U32(a >> other)),
            U64(a) => Ok(U64(a >> other)),
            U128(a) => Ok(U128(a >> other)),
            I8(a) => Ok(I8(a >> other)),
            I16(a) => Ok(I16(a >> other)),
            I32(a) => Ok(I32(a >> other)),
            I64(a) => Ok(I64(a >> other)),
            I128(a) => Ok(I128(a >> other)),
            USize(a) => Ok(USize(a >> other)),
            ISize(a) => Ok(ISize(a >> other)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> BitOr for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn bitor(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8(a | b)),
            (U16(a), U16(b)) => Ok(U16(a | b)),
            (U32(a), U32(b)) => Ok(U32(a | b)),
            (U64(a), U64(b)) => Ok(U64(a | b)),
            (U128(a), U128(b)) => Ok(U128(a | b)),
            (I8(a), I8(b)) => Ok(I8(a | b)),
            (I16(a), I16(b)) => Ok(I16(a | b)),
            (I32(a), I32(b)) => Ok(I32(a | b)),
            (I64(a), I64(b)) => Ok(I64(a | b)),
            (I128(a), I128(b)) => Ok(I128(a | b)),
            (USize(a), USize(b)) => Ok(USize(a | b)),
            (ISize(a), ISize(b)) => Ok(ISize(a | b)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> BitXor for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn bitxor(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8(a ^ b)),
            (U16(a), U16(b)) => Ok(U16(a ^ b)),
            (U32(a), U32(b)) => Ok(U32(a ^ b)),
            (U64(a), U64(b)) => Ok(U64(a ^ b)),
            (U128(a), U128(b)) => Ok(U128(a ^ b)),
            (I8(a), I8(b)) => Ok(I8(a ^ b)),
            (I16(a), I16(b)) => Ok(I16(a ^ b)),
            (I32(a), I32(b)) => Ok(I32(a ^ b)),
            (I64(a), I64(b)) => Ok(I64(a ^ b)),
            (I128(a), I128(b)) => Ok(I128(a ^ b)),
            (USize(a), USize(b)) => Ok(USize(a ^ b)),
            (ISize(a), ISize(b)) => Ok(ISize(a ^ b)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> BitAnd for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn bitand(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8(a & b)),
            (U16(a), U16(b)) => Ok(U16(a & b)),
            (U32(a), U32(b)) => Ok(U32(a & b)),
            (U64(a), U64(b)) => Ok(U64(a & b)),
            (U128(a), U128(b)) => Ok(U128(a & b)),
            (I8(a), I8(b)) => Ok(I8(a & b)),
            (I16(a), I16(b)) => Ok(I16(a & b)),
            (I32(a), I32(b)) => Ok(I32(a & b)),
            (I64(a), I64(b)) => Ok(I64(a & b)),
            (I128(a), I128(b)) => Ok(I128(a & b)),
            (USize(a), USize(b)) => Ok(USize(a & b)),
            (ISize(a), ISize(b)) => Ok(ISize(a & b)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}

impl<'ir> Div for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn div(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        let result = match (self, other) {
            (U8(a), U8(b)) => a.checked_div(b).map(U8),
            (U16(a), U16(b)) => a.checked_div(b).map(U16),
            (U32(a), U32(b)) => a.checked_div(b).map(U32),
            (U64(a), U64(b)) => a.checked_div(b).map(U64),
            (U128(a), U128(b)) => a.checked_div(b).map(U128),
            (I8(a), I8(b)) => a.checked_div(b).map(I8),
            (I16(a), I16(b)) => a.checked_div(b).map(I16),
            (I32(a), I32(b)) => a.checked_div(b).map(I32),
            (I64(a), I64(b)) => a.checked_div(b).map(I64),
            (I128(a), I128(b)) => a.checked_div(b).map(I128),
            (USize(a), USize(b)) => a.checked_div(b).map(USize),
            (ISize(a), ISize(b)) => a.checked_div(b).map(ISize),
            _ => None,
        };

        result.ok_or(ConstEvalError::DivisionByZero)
    }
}

impl<'ir> Rem for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn rem(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        let result = match (self, other) {
            (U8(a), U8(b)) => a.checked_rem(b).map(U8),
            (U16(a), U16(b)) => a.checked_rem(b).map(U16),
            (U32(a), U32(b)) => a.checked_rem(b).map(U32),
            (U64(a), U64(b)) => a.checked_rem(b).map(U64),
            (U128(a), U128(b)) => a.checked_rem(b).map(U128),
            (I8(a), I8(b)) => a.checked_rem(b).map(I8),
            (I16(a), I16(b)) => a.checked_rem(b).map(I16),
            (I32(a), I32(b)) => a.checked_rem(b).map(I32),
            (I64(a), I64(b)) => a.checked_rem(b).map(I64),
            (I128(a), I128(b)) => a.checked_rem(b).map(I128),
            (USize(a), USize(b)) => a.checked_rem(b).map(USize),
            (ISize(a), ISize(b)) => a.checked_rem(b).map(ISize),
            _ => None,
        };

        result.ok_or(ConstEvalError::DivisionByZero)
    }
}

pub struct ConstEvaluator<'ir> {
    ir: &'ir IrCtx<'ir>,
}

impl<'ir> ConstEvaluator<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self { ir }
    }

    fn cast(&self, inner: ExprP<'ir>, mut target: TyP<'ir>) -> Result<Value<'ir>> {
        let val = self.const_eval(inner)?;
        if inner.ty == target {
            return Ok(val);
        }

        if let Ty::Item(e) = target {
            if let Ok(e) = e.get_enum() {
                target = e.underlying_type;
            }
        }

        let promoted = match val {
            Value::U8(a) => Value::U128(a as u128),
            Value::U16(a) => Value::U128(a as u128),
            Value::U32(a) => Value::U128(a as u128),
            Value::U64(a) => Value::U128(a as u128),
            Value::U128(a) => Value::U128(a),
            Value::USize(a) => Value::U128(a as u128),
            Value::I8(a) => Value::I128(a as i128),
            Value::I16(a) => Value::I128(a as i128),
            Value::I32(a) => Value::I128(a as i128),
            Value::I64(a) => Value::I128(a as i128),
            Value::I128(a) => Value::I128(a),
            Value::ISize(a) => Value::I128(a as i128),
            Value::Bool(a) => Value::U128(if a { 1 } else { 0 }),
            _ => val,
        };

        match (promoted, target) {
            (Value::U128(a), Ty::Builtin(BuiltinType::U8)) => Ok(Value::U8(a as u8)),
            (Value::U128(a), Ty::Builtin(BuiltinType::U16)) => Ok(Value::U16(a as u16)),
            (Value::U128(a), Ty::Builtin(BuiltinType::U32)) => Ok(Value::U32(a as u32)),
            (Value::U128(a), Ty::Builtin(BuiltinType::U64)) => Ok(Value::U64(a as u64)),
            (Value::U128(a), Ty::Builtin(BuiltinType::U128)) => Ok(Value::U128(a)),
            (Value::U128(a), Ty::Builtin(BuiltinType::USize)) => Ok(Value::USize(a as usize)),
            (Value::U128(a), Ty::Builtin(BuiltinType::I8)) => Ok(Value::I8(a as i8)),
            (Value::U128(a), Ty::Builtin(BuiltinType::I16)) => Ok(Value::I16(a as i16)),
            (Value::U128(a), Ty::Builtin(BuiltinType::I32)) => Ok(Value::I32(a as i32)),
            (Value::U128(a), Ty::Builtin(BuiltinType::I64)) => Ok(Value::I64(a as i64)),
            (Value::U128(a), Ty::Builtin(BuiltinType::I128)) => Ok(Value::I128(a as i128)),
            (Value::U128(a), Ty::Builtin(BuiltinType::ISize)) => Ok(Value::ISize(a as isize)),
            (Value::I128(a), Ty::Builtin(BuiltinType::U8)) => Ok(Value::U8(a as u8)),
            (Value::I128(a), Ty::Builtin(BuiltinType::U16)) => Ok(Value::U16(a as u16)),
            (Value::I128(a), Ty::Builtin(BuiltinType::U32)) => Ok(Value::U32(a as u32)),
            (Value::I128(a), Ty::Builtin(BuiltinType::U64)) => Ok(Value::U64(a as u64)),
            (Value::I128(a), Ty::Builtin(BuiltinType::U128)) => Ok(Value::U128(a as u128)),
            (Value::I128(a), Ty::Builtin(BuiltinType::USize)) => Ok(Value::USize(a as usize)),
            (Value::I128(a), Ty::Builtin(BuiltinType::I8)) => Ok(Value::I8(a as i8)),
            (Value::I128(a), Ty::Builtin(BuiltinType::I16)) => Ok(Value::I16(a as i16)),
            (Value::I128(a), Ty::Builtin(BuiltinType::I32)) => Ok(Value::I32(a as i32)),
            (Value::I128(a), Ty::Builtin(BuiltinType::I64)) => Ok(Value::I64(a as i64)),
            (Value::I128(a), Ty::Builtin(BuiltinType::I128)) => Ok(Value::I128(a)),
            (Value::I128(a), Ty::Builtin(BuiltinType::ISize)) => Ok(Value::ISize(a as isize)),
            (Value::F64(a), Ty::Builtin(BuiltinType::F32)) => Ok(Value::F32(a)),
            (Value::F32(a), Ty::Builtin(BuiltinType::F64)) => Ok(Value::F64(a)),
            (Value::FunctionPointer(id), Ty::FunctionPointer(..)) => Ok(Value::FunctionPointer(id)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }

    pub fn const_eval(&self, expr: ExprP<'ir>) -> Result<Value<'ir>> {
        match &expr.kind {
            ExprKind::Void => Ok(Value::Void),
            ExprKind::Binary(op, lhs, rhs) => {
                let lhs = self.const_eval(lhs)?;

                // Special case for short-circuiting operators
                match (op, lhs) {
                    (BinOp::Or, Value::Bool(a)) => {
                        return if a { Ok(lhs) } else { self.const_eval(rhs) }
                    }
                    (BinOp::And, Value::Bool(a)) => {
                        return if a { self.const_eval(rhs) } else { Ok(lhs) }
                    }
                    (BinOp::Or | BinOp::And, _) => return Err(ConstEvalError::CompilerBug),
                    _ => {}
                };

                let rhs = self.const_eval(rhs)?;
                match op {
                    BinOp::BitAnd => lhs & rhs,
                    BinOp::BitOr => lhs | rhs,
                    BinOp::BitXor => lhs ^ rhs,
                    BinOp::Eq => lhs.equal(rhs),
                    BinOp::Neq => lhs.equal(rhs).and_then(|v| !v),
                    BinOp::Lt => Ok(Value::Bool(matches!(lhs.cmp(rhs)?, Ordering::Less))),
                    BinOp::LEq => Ok(Value::Bool(matches!(
                        lhs.cmp(rhs)?,
                        Ordering::Less | Ordering::Equal
                    ))),
                    BinOp::Gt => Ok(Value::Bool(matches!(lhs.cmp(rhs)?, Ordering::Greater))),
                    BinOp::GEq => Ok(Value::Bool(matches!(
                        lhs.cmp(rhs)?,
                        Ordering::Greater | Ordering::Equal
                    ))),
                    BinOp::LShift => lhs << rhs,
                    BinOp::RShift => lhs >> rhs,
                    BinOp::Plus => lhs + rhs,
                    BinOp::Minus => lhs - rhs,
                    BinOp::Mul => lhs * rhs,
                    BinOp::Div => lhs / rhs,
                    BinOp::Mod => lhs % rhs,
                    _ => Err(ConstEvalError::Unsupported),
                }
            }
            ExprKind::Unary(op, inner) => {
                let inner = self.const_eval(inner)?;

                match op {
                    UnOp::Not if matches!(inner, Value::Bool(_)) => !inner,
                    UnOp::Neg => -inner,
                    UnOp::BitNot if !matches!(inner, Value::Bool(_)) => !inner,
                    _ => Err(ConstEvalError::CompilerBug),
                }
            }
            ExprKind::Literal(value) => Ok(*value),
            ExprKind::Cast(inner) => self.cast(inner, expr.ty),
            ExprKind::If(cond, then, els) => {
                let cond = self.const_eval(cond)?;

                let cond_value = match cond {
                    Value::Bool(b) => b,
                    _ => return Err(ConstEvalError::CompilerBug),
                };

                if cond_value {
                    self.const_eval(then)
                } else {
                    self.const_eval(els)
                }
            }
            ExprKind::Tuple(exprs) => {
                let mut values = Vec::new();
                for (idx, init) in exprs.iter().enumerate() {
                    assert_eq!(idx, init.index);
                    values.push(self.const_eval(init.value)?);
                }
                Ok(Value::Tuple(
                    self.ir.arena.alloc_slice_fill_iter(values.into_iter()),
                ))
            }
            ExprKind::Array(elems) => {
                let mut values = Vec::new();
                for elem in *elems {
                    values.push(self.const_eval(elem)?);
                }
                Ok(Value::Array(
                    self.ir.arena.alloc_slice_fill_iter(values.into_iter()),
                ))
            }
            ExprKind::Struct(fields) => {
                // Last assignment wins
                let mut values = HashMap::default();
                for field in *fields {
                    values.insert(field.field, self.const_eval(field.value)?);
                }
                Ok(Value::Struct(
                    self.ir.arena.alloc_slice_fill_iter(values.into_iter()),
                ))
            }
            ExprKind::TupleIndex(tup, idx) => {
                let tup = self.const_eval(tup)?;
                match tup {
                    Value::Tuple(values) => Ok(values[*idx]),
                    _ => Err(ConstEvalError::CompilerBug),
                }
            }
            ExprKind::Index(array, idx) => {
                let array = self.const_eval(array)?;
                let idx = self.const_eval(idx)?;
                match (array, idx) {
                    (Value::Array(values), Value::USize(idx)) => values
                        .get(idx)
                        .copied()
                        .ok_or(ConstEvalError::IndexOutOfBounds),
                    _ => Err(ConstEvalError::Unsupported),
                }
            }
            ExprKind::Field(r#struct, field) => {
                let r#struct = self.const_eval(r#struct)?;
                match r#struct {
                    Value::Struct(fields) => fields
                        .iter()
                        .find(|(f, _)| *f == *field)
                        .map(|(_, v)| *v)
                        .ok_or(ConstEvalError::UninitializedField),
                    _ => Err(ConstEvalError::Unsupported),
                }
            }
            ExprKind::Block(statements, ret) => {
                for stmt in *statements {
                    // You can have statements in constant expressions as long as they're constant expressions themselves (and therefore pure)
                    match stmt {
                        Statement::Expression(expr) => {
                            self.const_eval(expr)?;
                            assert!(expr.pure());
                        }
                        _ => return Err(ConstEvalError::Unsupported),
                    }
                }

                self.const_eval(ret)
            }
            ExprKind::Fn(item) => Ok(Value::FunctionPointer(item)),
            _ => Err(ConstEvalError::Unsupported),
        }
    }
}
