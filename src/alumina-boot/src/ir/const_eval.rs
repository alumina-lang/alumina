/// An interpreter for constant expressions. It's quite slow.
use crate::ast::BinOp;
use crate::common::{
    AluminaError, ArenaAllocatable, ByRef, CodeDiagnostic, CodeError, CodeErrorBuilder, HashMap,
};
use crate::diagnostics::DiagnosticsStack;
use crate::global_ctx::GlobalCtx;
use crate::ir::{BuiltinType, ExprKind, ExprP, Id, IrCtx, Item, Statement, Ty, TyP, UnOp};
use std::backtrace::Backtrace;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::hash::Hash;
use std::num::TryFromIntError;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};
use std::rc::Rc;

use thiserror::Error;

const MAX_RECURSION_DEPTH: usize = 100;
const MAX_ITERATIONS: usize = 100000;

#[derive(Debug, Clone, Copy)]
pub enum Value<'ir> {
    Void,
    Uninitialized,
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
    F32(f32),
    F64(f64),
    Bytes(&'ir [u8], usize),
    Tuple(&'ir [Value<'ir>]),
    Array(&'ir [Value<'ir>]),
    Struct(&'ir [(Id, Value<'ir>)]),
    FunctionPointer(super::ItemP<'ir>),
    Pointer(LValue<'ir>, TyP<'ir>),
    #[allow(clippy::enum_variant_names)]
    LValue(LValue<'ir>),
}

impl PartialEq for Value<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Void, Value::Void) => true,
            (Value::Uninitialized, Value::Uninitialized) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::U8(a), Value::U8(b)) => a == b,
            (Value::U16(a), Value::U16(b)) => a == b,
            (Value::U32(a), Value::U32(b)) => a == b,
            (Value::U64(a), Value::U64(b)) => a == b,
            (Value::U128(a), Value::U128(b)) => a == b,
            (Value::I8(a), Value::I8(b)) => a == b,
            (Value::I16(a), Value::I16(b)) => a == b,
            (Value::I32(a), Value::I32(b)) => a == b,
            (Value::I64(a), Value::I64(b)) => a == b,
            (Value::I128(a), Value::I128(b)) => a == b,
            (Value::USize(a), Value::USize(b)) => a == b,
            (Value::ISize(a), Value::ISize(b)) => a == b,
            (Value::F32(a), Value::F32(b)) => a.to_bits() == b.to_bits(),
            (Value::F64(a), Value::F64(b)) => a.to_bits() == b.to_bits(),
            (Value::Bytes(a, a_len), Value::Bytes(b, b_len)) => a_len == b_len && a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::Struct(a), Value::Struct(b)) => a == b,
            (Value::FunctionPointer(a), Value::FunctionPointer(b)) => a == b,
            (Value::Pointer(a, _), Value::Pointer(b, _)) => a == b,
            (Value::LValue(a), Value::LValue(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Value<'_> {}
impl Hash for Value<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Value::Void => state.write_u8(0),
            Value::Uninitialized => state.write_u8(1),
            Value::Bool(a) => {
                state.write_u8(2);
                state.write_u8(*a as u8);
            }
            Value::U8(a) => {
                state.write_u8(3);
                state.write_u8(*a);
            }
            Value::U16(a) => {
                state.write_u8(4);
                state.write_u16(*a);
            }
            Value::U32(a) => {
                state.write_u8(5);
                state.write_u32(*a);
            }
            Value::U64(a) => {
                state.write_u8(6);
                state.write_u64(*a);
            }
            Value::U128(a) => {
                state.write_u8(7);
                state.write_u128(*a);
            }
            Value::I8(a) => {
                state.write_u8(8);
                state.write_u8(*a as u8);
            }
            Value::I16(a) => {
                state.write_u8(9);
                state.write_u16(*a as u16);
            }
            Value::I32(a) => {
                state.write_u8(10);
                state.write_u32(*a as u32);
            }
            Value::I64(a) => {
                state.write_u8(11);
                state.write_u64(*a as u64);
            }
            Value::I128(a) => {
                state.write_u8(12);
                state.write_u128(*a as u128);
            }
            Value::USize(a) => {
                state.write_u8(13);
                state.write_usize(*a);
            }
            Value::ISize(a) => {
                state.write_u8(14);
                state.write_usize(*a as usize);
            }
            Value::F32(a) => {
                state.write_u8(15);
                state.write_u32(a.to_bits());
            }
            Value::F64(a) => {
                state.write_u8(16);
                state.write_u64(a.to_bits());
            }
            Value::Bytes(a, a_len) => {
                state.write_u8(17);
                a.hash(state);
                a_len.hash(state);
            }
            Value::Tuple(a) => {
                state.write_u8(18);
                a.hash(state);
            }
            Value::Array(a) => {
                state.write_u8(19);
                a.hash(state);
            }
            Value::Struct(a) => {
                state.write_u8(20);
                a.hash(state);
            }
            Value::FunctionPointer(a) => {
                state.write_u8(21);
                a.hash(state);
            }
            Value::Pointer(a, ty) => {
                state.write_u8(22);
                a.hash(state);
                ty.hash(state);
            }
            Value::LValue(a) => {
                state.write_u8(23);
                a.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LValue<'ir> {
    Const(ItemP<'ir>),
    Variable(Id),
    Alloc(Id),
    Field(&'ir LValue<'ir>, Id),
    Index(&'ir LValue<'ir>, usize),
    TupleIndex(&'ir LValue<'ir>, usize),
}

#[derive(Debug, Error, Clone, Hash, PartialEq, Eq)]
pub enum ConstEvalErrorKind {
    #[error("not constant or unsupported expression")]
    Unsupported,
    #[error("function `{}` is not supported in constant context", .0)]
    UnsupportedFunction(String),
    #[error("ice: encountered a branch that should have been rejected during type checking")]
    CompilerBug(ByRef<Backtrace>),
    #[error("performing pointer operations on pointers of different provenance")]
    ProvenanceMismatch,
    #[error("accessing memory location via an incompatible pointer")]
    IncompatiblePointer,
    #[error("index out of bounds")]
    IndexOutOfBounds,
    #[error("arithmetic overflow")]
    ArithmeticOverflow,
    #[error("reached unreachable code")]
    ToReachTheUnreachableStar,
    #[error("division by zero")]
    DivisionByZero,
    #[error("max recursion depth exceeded")]
    TooDeep,
    #[error("max iterations exceeded")]
    TooManyIterations,
    #[error("contains pointer to a local variable")]
    LValueLeak,
    #[error("dynamically allocated memory used after being freed")]
    UseAfterFree,
    #[error("invalid pointer used to free memory")]
    InvalidFree,
    #[error("function call with an wrong signature")]
    InvalidCall,

    // These are not errors, but they are used to signal that the evaluation should stop.
    // They are bugs if they leak to the caller
    #[error("ice: non-local jump")]
    Jump(Id),
    #[error("ice: return from a constant expression")]
    Return,
    #[error("ice: stop iteration")]
    StopIteration,
}

impl From<ConstEvalErrorKind> for CodeDiagnostic {
    fn from(kind: ConstEvalErrorKind) -> Self {
        CodeDiagnostic::CannotConstEvaluate(kind)
    }
}

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

macro_rules! unsupported {
    ($self:expr) => {
        return Err(ConstEvalErrorKind::Unsupported).with_backtrace(&$self.diag)
    };
}

macro_rules! bug {
    ($self:expr) => {{
        return Err(ConstEvalErrorKind::CompilerBug(Backtrace::capture().into()))
            .with_backtrace(&$self.diag);
    }};
}

pub(crate) use numeric_of_kind;

use super::builder::TypeBuilder;
use super::{IntrinsicValueKind, ItemP};

impl<'ir> Value<'ir> {
    fn equals(self, other: Value<'ir>) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
            (Value::F32(a), Value::F32(b)) => Ok(Value::Bool(a == b)),
            (Value::F64(a), Value::F64(b)) => Ok(Value::Bool(a == b)),
            (Value::USize(a), Value::USize(b)) => Ok(Value::Bool(a == b)),
            (Value::ISize(a), Value::ISize(b)) => Ok(Value::Bool(a == b)),
            (Value::Bytes(a_slice, a_index), Value::Bytes(b_slice, b_index)) => {
                Ok(Value::Bool(a_slice == b_slice && a_index == b_index))
            }
            (Value::FunctionPointer(a), Value::FunctionPointer(b)) => Ok(Value::Bool(a == b)),
            (Value::Pointer(a, _), Value::Pointer(b, _)) => Ok(Value::Bool(a == b)),
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }

    fn compare(self, other: Value<'ir>) -> Result<Option<Ordering>, ConstEvalErrorKind> {
        match (self, other) {
            (Value::U8(a), Value::U8(b)) => Ok(a.partial_cmp(&b)),
            (Value::U16(a), Value::U16(b)) => Ok(a.partial_cmp(&b)),
            (Value::U32(a), Value::U32(b)) => Ok(a.partial_cmp(&b)),
            (Value::U64(a), Value::U64(b)) => Ok(a.partial_cmp(&b)),
            (Value::U128(a), Value::U128(b)) => Ok(a.partial_cmp(&b)),
            (Value::I8(a), Value::I8(b)) => Ok(a.partial_cmp(&b)),
            (Value::I16(a), Value::I16(b)) => Ok(a.partial_cmp(&b)),
            (Value::I32(a), Value::I32(b)) => Ok(a.partial_cmp(&b)),
            (Value::I64(a), Value::I64(b)) => Ok(a.partial_cmp(&b)),
            (Value::I128(a), Value::I128(b)) => Ok(a.partial_cmp(&b)),
            (Value::F32(a), Value::F32(b)) => Ok(a.partial_cmp(&b)),
            (Value::F64(a), Value::F64(b)) => Ok(a.partial_cmp(&b)),
            (Value::USize(a), Value::USize(b)) => Ok(a.partial_cmp(&b)),
            (Value::ISize(a), Value::ISize(b)) => Ok(a.partial_cmp(&b)),
            (Value::Bool(a), Value::Bool(b)) => Ok(a.partial_cmp(&b)),
            (Value::Bytes(a_slice, a_index), Value::Bytes(b_slice, b_index)) => {
                if a_slice == b_slice {
                    Ok(a_index.partial_cmp(&b_index))
                } else {
                    Err(ConstEvalErrorKind::ProvenanceMismatch)
                }
            }
            (Value::Pointer(a, _), Value::Pointer(b, _)) => match (a, b) {
                (LValue::Const(a), LValue::Const(b)) => {
                    if a == b {
                        Ok(Some(Ordering::Equal))
                    } else {
                        Err(ConstEvalErrorKind::ProvenanceMismatch)
                    }
                }
                (LValue::Variable(a), LValue::Variable(b))
                | (LValue::Alloc(a), LValue::Alloc(b)) => {
                    if a == b {
                        Ok(Some(Ordering::Equal))
                    } else {
                        Err(ConstEvalErrorKind::ProvenanceMismatch)
                    }
                }
                (LValue::Field(a, a_id), LValue::Field(b, b_id)) => {
                    if a == b && a_id == b_id {
                        Ok(Some(Ordering::Equal))
                    } else {
                        Err(ConstEvalErrorKind::ProvenanceMismatch)
                    }
                }
                (LValue::TupleIndex(a, a_idx), LValue::TupleIndex(b, b_idx)) => {
                    if a == b && a_idx == b_idx {
                        Ok(Some(Ordering::Equal))
                    } else {
                        Err(ConstEvalErrorKind::ProvenanceMismatch)
                    }
                }
                (LValue::Index(a, a_idx), LValue::Index(b, b_idx)) => {
                    if a == b {
                        Ok(a_idx.partial_cmp(&b_idx))
                    } else {
                        Err(ConstEvalErrorKind::ProvenanceMismatch)
                    }
                }
                _ => Err(ConstEvalErrorKind::Unsupported),
            },
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Add for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn add(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I16(a), I16(b)) => a
                .checked_add(b)
                .map(I16)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I32(a), I32(b)) => a
                .checked_add(b)
                .map(I32)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I64(a), I64(b)) => a
                .checked_add(b)
                .map(I64)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I128(a), I128(b)) => a
                .checked_add(b)
                .map(I128)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (ISize(a), ISize(b)) => a
                .checked_add(b)
                .map(ISize)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (F32(a), F32(b)) => Ok(F32(a + b)),
            (F64(a), F64(b)) => Ok(F64(a + b)),
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Sub for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn sub(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I16(a), I16(b)) => a
                .checked_sub(b)
                .map(I16)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I32(a), I32(b)) => a
                .checked_sub(b)
                .map(I32)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I64(a), I64(b)) => a
                .checked_sub(b)
                .map(I64)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I128(a), I128(b)) => a
                .checked_sub(b)
                .map(I128)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (ISize(a), ISize(b)) => a
                .checked_sub(b)
                .map(ISize)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (F32(a), F32(b)) => Ok(F32(a - b)),
            (F64(a), F64(b)) => Ok(F64(a - b)),
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Mul for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn mul(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I16(a), I16(b)) => a
                .checked_mul(b)
                .map(I16)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I32(a), I32(b)) => a
                .checked_mul(b)
                .map(I32)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I64(a), I64(b)) => a
                .checked_mul(b)
                .map(I64)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (I128(a), I128(b)) => a
                .checked_mul(b)
                .map(I128)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (ISize(a), ISize(b)) => a
                .checked_mul(b)
                .map(ISize)
                .ok_or(ConstEvalErrorKind::ArithmeticOverflow),
            (F32(a), F32(b)) => Ok(F32(a * b)),
            (F64(a), F64(b)) => Ok(F64(a * b)),
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Shl<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn shl(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
        use Value::*;

        let other: Result<u32, TryFromIntError> = match other {
            U8(other) => Ok(other as _),
            U16(other) => Ok(other as _),
            U32(other) => Ok(other),
            U64(other) => other.try_into(),
            U128(other) => other.try_into(),
            USize(other) => other.try_into(),
            I8(other) => other.try_into(),
            I16(other) => other.try_into(),
            I32(other) => other.try_into(),
            I64(other) => other.try_into(),
            I128(other) => other.try_into(),
            ISize(other) => other.try_into(),
            _ => return Err(ConstEvalErrorKind::CompilerBug(Backtrace::capture().into())),
        };
        let other = other.map_err(|_| ConstEvalErrorKind::ArithmeticOverflow)?;

        let ret = match self {
            U8(a) => a.checked_shl(other).map(U8),
            U16(a) => a.checked_shl(other).map(U16),
            U32(a) => a.checked_shl(other).map(U32),
            U64(a) => a.checked_shl(other).map(U64),
            U128(a) => a.checked_shl(other).map(U128),
            USize(a) => a.checked_shl(other).map(USize),
            I8(a) => a.checked_shl(other).map(I8),
            I16(a) => a.checked_shl(other).map(I16),
            I32(a) => a.checked_shl(other).map(I32),
            I64(a) => a.checked_shl(other).map(I64),
            I128(a) => a.checked_shl(other).map(I128),
            ISize(a) => a.checked_shl(other).map(ISize),
            _ => return Err(ConstEvalErrorKind::Unsupported),
        };

        ret.ok_or(ConstEvalErrorKind::ArithmeticOverflow)
    }
}

impl<'ir> Neg for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn neg(self) -> Result<Value<'ir>, ConstEvalErrorKind> {
        use Value::*;

        match self {
            I8(a) => Ok(I8(-a)),
            I16(a) => Ok(I16(-a)),
            I32(a) => Ok(I32(-a)),
            I64(a) => Ok(I64(-a)),
            I128(a) => Ok(I128(-a)),
            ISize(a) => Ok(ISize(-a)),
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Not for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn not(self) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Shr<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn shr(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
        use Value::*;

        let other: Result<u32, TryFromIntError> = match other {
            U8(other) => Ok(other as _),
            U16(other) => Ok(other as _),
            U32(other) => Ok(other),
            U64(other) => other.try_into(),
            U128(other) => other.try_into(),
            USize(other) => other.try_into(),
            I8(other) => other.try_into(),
            I16(other) => other.try_into(),
            I32(other) => other.try_into(),
            I64(other) => other.try_into(),
            I128(other) => other.try_into(),
            ISize(other) => other.try_into(),
            _ => return Err(ConstEvalErrorKind::CompilerBug(Backtrace::capture().into())),
        };
        let other = other.map_err(|_| ConstEvalErrorKind::ArithmeticOverflow)?;
        let ret = match self {
            U8(a) => a.checked_shr(other).map(U8),
            U16(a) => a.checked_shr(other).map(U16),
            U32(a) => a.checked_shr(other).map(U32),
            U64(a) => a.checked_shr(other).map(U64),
            U128(a) => a.checked_shr(other).map(U128),
            USize(a) => a.checked_shr(other).map(USize),
            I8(a) => a.checked_shr(other).map(I8),
            I16(a) => a.checked_shr(other).map(I16),
            I32(a) => a.checked_shr(other).map(I32),
            I64(a) => a.checked_shr(other).map(I64),
            I128(a) => a.checked_shr(other).map(I128),
            ISize(a) => a.checked_shr(other).map(ISize),
            _ => return Err(ConstEvalErrorKind::Unsupported),
        };

        ret.ok_or(ConstEvalErrorKind::ArithmeticOverflow)
    }
}

impl<'ir> BitOr for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn bitor(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> BitXor for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn bitxor(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> BitAnd for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn bitand(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
            _ => Err(ConstEvalErrorKind::Unsupported),
        }
    }
}

impl<'ir> Div for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn div(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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
            (F32(a), F32(b)) => Some(F32(a / b)),
            (F64(a), F64(b)) => Some(F64(a / b)),
            _ => None,
        };

        result.ok_or(ConstEvalErrorKind::DivisionByZero)
    }
}

impl<'ir> Rem for Value<'ir> {
    type Output = Result<Value<'ir>, ConstEvalErrorKind>;
    fn rem(self, other: Value) -> Result<Value<'ir>, ConstEvalErrorKind> {
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

        result.ok_or(ConstEvalErrorKind::DivisionByZero)
    }
}

struct ConstEvalCtxInner<'ir> {
    variables: HashMap<Id, Value<'ir>>,
    steps_remaining: usize,
}

#[derive(Clone)]
pub struct ConstEvalCtx<'ir> {
    global_ctx: GlobalCtx,
    ir: &'ir IrCtx<'ir>,
    malloc_bag: MallocBag<'ir>,
    inner: Rc<RefCell<ConstEvalCtxInner<'ir>>>,
}

struct MallocBagInner<'ir> {
    variables: HashMap<Id, Value<'ir>>,
}

#[derive(Clone)]
pub struct MallocBag<'ir> {
    inner: Rc<RefCell<MallocBagInner<'ir>>>,
}

impl<'ir> MallocBag<'ir> {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(MallocBagInner {
                variables: HashMap::default(),
            })),
        }
    }

    pub fn define(&self, id: Id, value: Value<'ir>) {
        self.inner.borrow_mut().variables.insert(id, value);
    }

    pub fn assign(&self, id: Id, value: Value<'ir>) -> Option<Value<'ir>> {
        let mut inner = self.inner.borrow_mut();
        match inner.variables.entry(id) {
            std::collections::hash_map::Entry::Occupied(mut val) => Some(val.insert(value)),
            std::collections::hash_map::Entry::Vacant(_) => None,
        }
    }

    pub fn free(&self, id: Id) -> Option<Value<'ir>> {
        self.inner.borrow_mut().variables.remove(&id)
    }

    pub fn get(&self, id: Id) -> Option<Value<'ir>> {
        self.inner.borrow().variables.get(&id).cloned()
    }
}

impl<'ir> ConstEvalCtx<'ir> {
    pub fn new(global_ctx: GlobalCtx, ir: &'ir IrCtx<'ir>, malloc_bag: MallocBag<'ir>) -> Self {
        Self {
            global_ctx,
            ir,
            malloc_bag,
            inner: Rc::new(RefCell::new(ConstEvalCtxInner {
                variables: HashMap::default(),
                steps_remaining: MAX_ITERATIONS,
            })),
        }
    }

    pub fn step(&self) -> Result<(), ConstEvalErrorKind> {
        let mut inner = self.inner.borrow_mut();
        if inner.steps_remaining == 0 {
            return Err(ConstEvalErrorKind::TooManyIterations);
        }
        inner.steps_remaining -= 1;
        Ok(())
    }

    pub fn define(&self, id: Id, value: Value<'ir>) {
        self.inner.borrow_mut().variables.insert(id, value);
    }

    pub fn declare(&self, id: Id, ty: TyP<'ir>) {
        self.inner
            .borrow_mut()
            .variables
            .insert(id, make_uninitialized(self.ir, ty));
    }

    pub fn assign(&self, id: Id, value: Value<'ir>) {
        self.inner.borrow_mut().variables.insert(id, value);
    }

    pub fn load_var(&self, id: Id) -> Value<'ir> {
        *self
            .inner
            .borrow_mut()
            .variables
            .entry(id)
            .or_insert(Value::Uninitialized)
    }
}

pub struct ConstEvaluator<'ir> {
    ir: &'ir IrCtx<'ir>,
    ctx: ConstEvalCtx<'ir>,
    return_slot: Option<Value<'ir>>,
    remaining_depth: usize,
    remapped_variables: HashMap<Id, Id>,
    types: TypeBuilder<'ir>,
    diag: DiagnosticsStack,
    codegen: bool,
}

impl<'ir> ConstEvaluator<'ir> {
    pub fn new<I>(
        global_ctx: GlobalCtx,
        diag: DiagnosticsStack,
        malloc_bag: MallocBag<'ir>,
        ir: &'ir IrCtx<'ir>,
        local_types: I,
    ) -> Self
    where
        I: IntoIterator<Item = (Id, TyP<'ir>)>,
    {
        let ctx = ConstEvalCtx::new(global_ctx, ir, malloc_bag);
        for (id, ty) in local_types {
            ctx.declare(id, ty);
        }

        Self {
            ir,
            return_slot: None,
            remaining_depth: MAX_RECURSION_DEPTH,
            remapped_variables: Default::default(),
            diag,
            types: TypeBuilder::new(ir),
            ctx,
            codegen: false,
        }
    }

    pub fn for_codegen<I>(
        global_ctx: GlobalCtx,
        diag: DiagnosticsStack,
        malloc_bag: MallocBag<'ir>,
        ir: &'ir IrCtx<'ir>,
        local_types: I,
    ) -> Self
    where
        I: IntoIterator<Item = (Id, TyP<'ir>)>,
    {
        let mut ret = Self::new(global_ctx, diag, malloc_bag, ir, local_types);
        ret.codegen = true;
        ret
    }

    fn make_child(&self, remapped_variables: HashMap<Id, Id>) -> Result<Self, AluminaError> {
        Ok(Self {
            ir: self.ir,
            ctx: self.ctx.clone(),
            return_slot: None,
            remaining_depth: self
                .remaining_depth
                .checked_sub(1)
                .ok_or(ConstEvalErrorKind::TooDeep)
                .with_backtrace(&self.diag)?,
            remapped_variables,
            types: TypeBuilder::new(self.ir),
            diag: self.diag.fork(),
            codegen: self.codegen,
        })
    }

    fn cast(
        &mut self,
        inner: ExprP<'ir>,
        mut target: TyP<'ir>,
    ) -> Result<Value<'ir>, AluminaError> {
        let val = self.const_eval_rvalue(inner)?;
        if inner.ty == target {
            return Ok(val);
        }

        if let Ty::Item(e) = target {
            if let Ok(e) = e.get_enum() {
                target = e.underlying_ty;
            }
        }

        let promoted = match val {
            Value::U8(a) => Value::U128(a as u128),
            Value::U16(a) => Value::U128(a as u128),
            Value::U32(a) => Value::U128(a as u128),
            Value::U64(a) => Value::U128(a as u128),
            Value::USize(a) => Value::U128(a as u128),
            Value::I8(a) => Value::I128(a as i128),
            Value::I16(a) => Value::I128(a as i128),
            Value::I32(a) => Value::I128(a as i128),
            Value::I64(a) => Value::I128(a as i128),
            Value::I128(a) => Value::I128(a),
            Value::ISize(a) => Value::I128(a as i128),
            Value::Bool(a) => Value::U128(a as u128),
            Value::F32(a) => Value::F64(a as f64),
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
            (Value::U128(a), Ty::Builtin(BuiltinType::F64)) => Ok(Value::F64(a as f64)),
            (Value::U128(a), Ty::Builtin(BuiltinType::F32)) => Ok(Value::F32(a as f32)),

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
            (Value::I128(a), Ty::Builtin(BuiltinType::F64)) => Ok(Value::F64(a as f64)),
            (Value::I128(a), Ty::Builtin(BuiltinType::F32)) => Ok(Value::F32(a as f32)),

            (Value::F64(a), Ty::Builtin(BuiltinType::U8)) => Ok(Value::U8(a as u8)),
            (Value::F64(a), Ty::Builtin(BuiltinType::U16)) => Ok(Value::U16(a as u16)),
            (Value::F64(a), Ty::Builtin(BuiltinType::U32)) => Ok(Value::U32(a as u32)),
            (Value::F64(a), Ty::Builtin(BuiltinType::U64)) => Ok(Value::U64(a as u64)),
            (Value::F64(a), Ty::Builtin(BuiltinType::U128)) => Ok(Value::U128(a as u128)),
            (Value::F64(a), Ty::Builtin(BuiltinType::USize)) => Ok(Value::USize(a as usize)),
            (Value::F64(a), Ty::Builtin(BuiltinType::I8)) => Ok(Value::I8(a as i8)),
            (Value::F64(a), Ty::Builtin(BuiltinType::I16)) => Ok(Value::I16(a as i16)),
            (Value::F64(a), Ty::Builtin(BuiltinType::I32)) => Ok(Value::I32(a as i32)),
            (Value::F64(a), Ty::Builtin(BuiltinType::I64)) => Ok(Value::I64(a as i64)),
            (Value::F64(a), Ty::Builtin(BuiltinType::I128)) => Ok(Value::I128(a as i128)),
            (Value::F64(a), Ty::Builtin(BuiltinType::ISize)) => Ok(Value::ISize(a as isize)),

            (Value::F64(a), Ty::Builtin(BuiltinType::F32)) => Ok(Value::F32(a as f32)),

            (Value::FunctionPointer(id), Ty::FunctionPointer(..)) => Ok(Value::FunctionPointer(id)),
            (Value::Pointer(value, original_ty), Ty::Pointer(_, _)) => {
                Ok(Value::Pointer(value, original_ty))
            }
            _ => unsupported!(self),
        }
    }

    fn field(&mut self, r#struct: Value<'ir>, field: Id) -> Result<Value<'ir>, AluminaError> {
        match r#struct {
            Value::LValue(lv) => Ok(Value::LValue(LValue::Field(lv.alloc_on(self.ir), field))),
            Value::Struct(fields) => Ok(fields
                .iter()
                .find(|(f, _)| *f == field)
                .map(|(_, v)| *v)
                .unwrap_or(Value::Uninitialized)),
            _ => {
                unsupported!(self)
            }
        }
    }

    fn index(&mut self, array: Value<'ir>, idx: usize) -> Result<Value<'ir>, AluminaError> {
        match array {
            Value::LValue(lv) => Ok(Value::LValue(LValue::Index(lv.alloc_on(self.ir), idx))),
            Value::Array(values) => values
                .get(idx)
                .copied()
                .ok_or(ConstEvalErrorKind::IndexOutOfBounds)
                .with_backtrace(&self.diag),
            _ => unsupported!(self),
        }
    }

    fn tuple_index(&mut self, tup: Value<'ir>, idx: usize) -> Result<Value<'ir>, AluminaError> {
        match tup {
            Value::LValue(lv) => Ok(Value::LValue(LValue::TupleIndex(lv.alloc_on(self.ir), idx))),
            Value::Tuple(values) => Ok(values.get(idx).cloned().unwrap_or(Value::Uninitialized)),
            _ => bug!(self),
        }
    }

    pub fn const_eval(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>, AluminaError> {
        // public facing interface. we clean up things that should not appear in the IR
        let ret = self.const_eval_rvalue(expr)?;
        check_lvalue_leak(&ret).with_backtrace(&self.diag)?;
        Ok(ret)
    }

    fn materialize(&mut self, value: Value<'ir>) -> Result<Value<'ir>, AluminaError> {
        match value {
            Value::LValue(v) => self.materialize_lvalue(v),
            _ => Ok(value),
        }
    }

    fn const_eval_rvalue(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>, AluminaError> {
        self.const_eval_defered(expr)
            .and_then(|v| self.materialize(v))
    }

    fn eval_statements(&mut self, statements: &[Statement<'ir>]) -> Result<(), AluminaError> {
        let label_indexes: HashMap<Id, usize> = statements
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match s {
                Statement::Label(id) => Some((*id, i)),
                _ => None,
            })
            .collect();

        let mut ip = 0usize;
        while ip < statements.len() {
            match statements[ip] {
                Statement::Expression(expr) => {
                    match self.const_eval_rvalue(expr) {
                        Ok(_) => {}
                        Err(e) => {
                            let AluminaError::CodeErrors(ref v) = e else {
                                return Err(e);
                            };
                            let [CodeError {
                                kind:
                                    CodeDiagnostic::CannotConstEvaluate(ConstEvalErrorKind::Jump(label)),
                                ..
                            }] = v[..]
                            else {
                                return Err(e);
                            };

                            if let Some(new_ip) = label_indexes.get(&label) {
                                ip = *new_ip;
                                continue;
                            } else {
                                // Go up one level
                                return Err(e);
                            }
                        }
                    }
                }
                Statement::Label(_) => {}
            }
            ip += 1;
        }

        Ok(())
    }

    fn materialize_lvalue(&mut self, value: LValue<'ir>) -> Result<Value<'ir>, AluminaError> {
        match value {
            LValue::Const(item) => {
                let Ok(item) = item.get_const() else {
                    bug!(self)
                };
                Ok(item.value)
            }
            LValue::Variable(id) => Ok(self.ctx.load_var(id)),
            LValue::Alloc(id) => Ok(self
                .ctx
                .malloc_bag
                .get(id)
                .ok_or(ConstEvalErrorKind::UseAfterFree)
                .with_backtrace(&self.diag)?),
            LValue::Field(lvalue, field) => {
                let base = self.materialize_lvalue(*lvalue)?;
                self.field(base, field)
            }
            LValue::Index(lvalue, idx) => {
                let base = self.materialize_lvalue(*lvalue)?;
                self.index(base, idx)
            }
            LValue::TupleIndex(lvalue, idx) => {
                let base = self.materialize_lvalue(*lvalue)?;
                self.tuple_index(base, idx)
            }
        }
    }

    fn assign(&mut self, lhs: LValue<'ir>, value: Value<'ir>) -> Result<(), AluminaError> {
        match lhs {
            LValue::Const(_) => {
                // mono should reject assignment to const lvalue
                bug!(self)
            }
            LValue::Variable(id) => {
                self.ctx.assign(id, value);
                Ok(())
            }
            LValue::Alloc(id) => {
                if self.ctx.malloc_bag.assign(id, value).is_none() {
                    Err(ConstEvalErrorKind::UseAfterFree).with_backtrace(&self.diag)
                } else {
                    Ok(())
                }
            }
            LValue::Field(lvalue, field) => {
                let base = self.materialize_lvalue(*lvalue)?;

                match base {
                    Value::Struct(fields) => {
                        let new_fields: Vec<_> = fields
                            .iter()
                            .filter(|(f, _)| *f != field)
                            .copied()
                            .chain(std::iter::once((field, value)))
                            .collect();

                        self.assign(
                            *lvalue,
                            Value::Struct(self.ir.arena.alloc_slice_copy(&new_fields[..])),
                        )
                    }
                    _ => bug!(self),
                }
            }
            LValue::Index(lvalue, idx) => {
                let base = self.materialize_lvalue(*lvalue)?;

                match base {
                    Value::Array(values) => {
                        let new_values: Vec<_> = values
                            .iter()
                            .enumerate()
                            .map(|(i, v)| if i == idx { value } else { *v })
                            .collect();

                        self.assign(
                            *lvalue,
                            Value::Array(self.ir.arena.alloc_slice_copy(&new_values[..])),
                        )
                    }
                    _ => bug!(self),
                }
            }
            LValue::TupleIndex(lvalue, idx) => {
                let base = self.materialize_lvalue(*lvalue)?;

                match base {
                    Value::Tuple(values) => {
                        let new_values: Vec<_> = values
                            .iter()
                            .enumerate()
                            .map(|(i, v)| if i == idx { value } else { *v })
                            .collect();

                        self.assign(
                            *lvalue,
                            Value::Tuple(self.ir.arena.alloc_slice_copy(&new_values[..])),
                        )
                    }
                    _ => bug!(self),
                }
            }
        }
    }

    #[allow(unreachable_code)]
    fn const_eval_defered(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>, AluminaError> {
        // Comment this line to debug expressions not being evaluated
        // successfully
        self.const_eval_defered_inner(expr)
    }

    /// Variant of const-eval that leaves LValues in place
    fn const_eval_defered_inner(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>, AluminaError> {
        let _guard = self.diag.push_span(expr.span);

        self.ctx.step().with_backtrace(&self.diag)?;

        match &expr.kind {
            ExprKind::Nop => Ok(Value::Void),
            ExprKind::Binary(op, lhs_e, rhs_e) => {
                let lhs = self.const_eval_rvalue(lhs_e)?;

                // Special case for short-circuiting operators
                match (op, lhs) {
                    (BinOp::Or, Value::Bool(a)) => {
                        return if a {
                            Ok(lhs)
                        } else {
                            self.const_eval_rvalue(rhs_e)
                        }
                    }
                    (BinOp::And, Value::Bool(a)) => {
                        return if a {
                            self.const_eval_rvalue(rhs_e)
                        } else {
                            Ok(lhs)
                        }
                    }
                    (BinOp::Or | BinOp::And, _) => {
                        bug!(self)
                    }
                    _ => {}
                };

                let rhs = self.const_eval_rvalue(rhs_e)?;
                self.bin_op(lhs, lhs_e.ty, *op, rhs, rhs_e.ty)
            }
            ExprKind::Local(id) => Ok(Value::LValue(LValue::Variable(
                *self.remapped_variables.get(id).unwrap_or(id),
            ))),
            ExprKind::Unary(op, inner) => {
                let inner = self.const_eval_rvalue(inner)?;
                let ret = match op {
                    UnOp::Not if matches!(inner, Value::Bool(_)) => !inner,
                    UnOp::Neg => -inner,
                    UnOp::BitNot if !matches!(inner, Value::Bool(_)) => !inner,
                    _ => bug!(self),
                };

                ret.with_backtrace(&self.diag)
            }
            ExprKind::Ref(value) => match self.const_eval_defered(value)? {
                Value::LValue(lvalue) => Ok(Value::Pointer(lvalue, value.ty)),
                _ => unsupported!(self),
            },
            ExprKind::Deref(value1) => {
                let value = self.const_eval_rvalue(value1)?;
                match value {
                    Value::Pointer(lvalue, original_ty) => {
                        if expr.ty != original_ty {
                            Err(ConstEvalErrorKind::IncompatiblePointer).with_backtrace(&self.diag)
                        } else {
                            Ok(Value::LValue(lvalue))
                        }
                    }
                    Value::Bytes(arr, off) => {
                        if off >= arr.len() {
                            return Err(ConstEvalErrorKind::IndexOutOfBounds)
                                .with_backtrace(&self.diag);
                        }

                        Ok(Value::U8(arr[off]))
                    }
                    _ => unsupported!(self),
                }
            }
            ExprKind::Lit(value) => Ok(*value),
            ExprKind::Cast(inner) => self.cast(inner, expr.ty),
            ExprKind::If(cond, then, els, _) => {
                let condv = self.const_eval_rvalue(cond)?;

                let cond_value = match condv {
                    Value::Bool(b) => b,
                    _ => unsupported!(self),
                };

                if cond_value {
                    self.const_eval_rvalue(then)
                } else {
                    self.const_eval_rvalue(els)
                }
            }
            ExprKind::Tuple(exprs) => {
                let mut values = Vec::new();
                for (idx, init) in exprs.iter().enumerate() {
                    assert_eq!(idx, init.index);
                    values.push(self.const_eval_rvalue(init.value)?);
                }
                Ok(Value::Tuple(self.ir.arena.alloc_slice_fill_iter(values)))
            }
            ExprKind::Array(elems) => {
                let mut values = Vec::new();
                for elem in *elems {
                    values.push(self.const_eval_rvalue(elem)?);
                }
                Ok(Value::Array(self.ir.arena.alloc_slice_fill_iter(values)))
            }
            ExprKind::Goto(id) => Err(ConstEvalErrorKind::Jump(*id)).with_backtrace(&self.diag),
            ExprKind::Struct(fields) => {
                // Last assignment wins
                let mut values = HashMap::default();
                for field in *fields {
                    values.insert(field.field, self.const_eval_rvalue(field.value)?);
                }
                Ok(Value::Struct(self.ir.arena.alloc_slice_fill_iter(values)))
            }
            ExprKind::TupleIndex(tup, idx) => {
                let tup = self.const_eval_defered(tup)?;
                self.tuple_index(tup, *idx)
            }
            ExprKind::Index(array, idx) => {
                let array = self.const_eval_defered(array)?;
                let idx = match self.const_eval_rvalue(idx)? {
                    Value::USize(idx) => idx,
                    _ => bug!(self),
                };
                self.index(array, idx)
            }
            ExprKind::Field(r#struct, field) => {
                let r#struct = self.const_eval_defered(r#struct)?;
                self.field(r#struct, *field)
            }
            ExprKind::Assign(lhs, rhs) => {
                let lhs = self.const_eval_defered(lhs)?;
                let rhs = self.const_eval_rvalue(rhs)?;
                match lhs {
                    Value::LValue(lvalue) => {
                        self.assign(lvalue, rhs)?;
                        Ok(Value::Void)
                    }
                    _ => bug!(self),
                }
            }
            ExprKind::AssignOp(op, lhs_e, rhs_e) => {
                let lhs = self.const_eval_defered(lhs_e)?;
                let rhs = self.const_eval_rvalue(rhs_e)?;
                match lhs {
                    Value::LValue(lvalue) => {
                        let normalized = self.materialize(lhs)?;
                        let res = self.bin_op(normalized, lhs_e.ty, *op, rhs, rhs_e.ty)?;
                        self.assign(lvalue, res)?;
                        Ok(Value::Void)
                    }
                    _ => bug!(self),
                }
            }
            ExprKind::Block(statements, ret) => {
                self.eval_statements(statements)?;
                self.const_eval_rvalue(ret)
            }
            ExprKind::Intrinsic(kind) => match kind {
                IntrinsicValueKind::Uninitialized => Ok(make_uninitialized(self.ir, expr.ty)),
                IntrinsicValueKind::Dangling(..) => Ok(Value::Uninitialized),
                IntrinsicValueKind::Volatile(inner) => self.const_eval_defered(inner),
                IntrinsicValueKind::SizeOfLike(_, _) => unsupported!(self),
                IntrinsicValueKind::Transmute(inner) => {
                    let inner = self.const_eval_rvalue(inner)?;

                    // Very limited transmutations
                    match (inner, expr.ty) {
                        (Value::U8(a), Ty::Builtin(BuiltinType::I8)) => Ok(Value::I8(a as i8)),
                        (Value::U16(a), Ty::Builtin(BuiltinType::I16)) => Ok(Value::I16(a as i16)),
                        (Value::U32(a), Ty::Builtin(BuiltinType::I32)) => Ok(Value::I32(a as i32)),
                        (Value::U64(a), Ty::Builtin(BuiltinType::I64)) => Ok(Value::I64(a as i64)),
                        (Value::U128(a), Ty::Builtin(BuiltinType::I128)) => {
                            Ok(Value::I128(a as i128))
                        }
                        (Value::USize(a), Ty::Builtin(BuiltinType::ISize)) => {
                            Ok(Value::ISize(a as isize))
                        }

                        (Value::I8(a), Ty::Builtin(BuiltinType::U8)) => Ok(Value::U8(a as u8)),
                        (Value::I16(a), Ty::Builtin(BuiltinType::U16)) => Ok(Value::U16(a as u16)),
                        (Value::I32(a), Ty::Builtin(BuiltinType::U32)) => Ok(Value::U32(a as u32)),
                        (Value::I64(a), Ty::Builtin(BuiltinType::U64)) => Ok(Value::U64(a as u64)),
                        (Value::I128(a), Ty::Builtin(BuiltinType::U128)) => {
                            Ok(Value::U128(a as u128))
                        }
                        (Value::ISize(a), Ty::Builtin(BuiltinType::USize)) => {
                            Ok(Value::USize(a as usize))
                        }

                        (Value::F64(a), Ty::Builtin(BuiltinType::U64)) => {
                            Ok(Value::U64(a.to_bits()))
                        }
                        (Value::F64(a), Ty::Builtin(BuiltinType::I64)) => {
                            Ok(Value::I64(a.to_bits() as i64))
                        }
                        (Value::F32(a), Ty::Builtin(BuiltinType::U32)) => {
                            Ok(Value::U32(a.to_bits()))
                        }
                        (Value::F32(a), Ty::Builtin(BuiltinType::I32)) => {
                            Ok(Value::I32(a.to_bits() as i32))
                        }

                        (Value::U64(a), Ty::Builtin(BuiltinType::F64)) => {
                            Ok(Value::F64(f64::from_bits(a)))
                        }
                        (Value::I64(a), Ty::Builtin(BuiltinType::F64)) => {
                            Ok(Value::F64(f64::from_bits(a as u64)))
                        }
                        (Value::U32(a), Ty::Builtin(BuiltinType::F32)) => {
                            Ok(Value::F32(f32::from_bits(a)))
                        }
                        (Value::I32(a), Ty::Builtin(BuiltinType::F32)) => {
                            Ok(Value::F32(f32::from_bits(a as u32)))
                        }
                        _ => unsupported!(self),
                    }
                }
                IntrinsicValueKind::Asm(_) => unsupported!(self),
                IntrinsicValueKind::FunctionLike(_) => unsupported!(self),
                IntrinsicValueKind::ConstLike(_) => unsupported!(self),
                IntrinsicValueKind::InConstContext => Ok(Value::Bool(
                    !self.codegen || self.ctx.global_ctx.has_option("force-const-context"),
                )),
                IntrinsicValueKind::StopIteration => {
                    Err(ConstEvalErrorKind::StopIteration).with_backtrace(&self.diag)
                }
                IntrinsicValueKind::ConstPanic(expr) => {
                    let value = self.const_eval_rvalue(expr)?;
                    match self.extract_constant_string_from_slice(&value) {
                        Some(msg) => {
                            return Err(CodeDiagnostic::ConstPanic(
                                std::str::from_utf8(msg).unwrap().to_string(),
                            ))
                            .with_backtrace(&self.diag)
                        }
                        None => {
                            unsupported!(self);
                        }
                    }
                }
                IntrinsicValueKind::ConstWrite(expr, is_warning) => {
                    let value = self.const_eval_rvalue(expr)?;
                    match self.extract_constant_string_from_slice(&value) {
                        Some(msg) => {
                            if *is_warning {
                                self.diag.warn(CodeDiagnostic::ConstMessage(
                                    std::str::from_utf8(msg).unwrap().to_string(),
                                ));
                            } else {
                                self.diag.note(CodeDiagnostic::ConstMessage(
                                    std::str::from_utf8(msg).unwrap().to_string(),
                                ));
                            }
                            Ok(Value::Void)
                        }
                        None => {
                            unsupported!(self);
                        }
                    }
                }
                IntrinsicValueKind::ConstAlloc(ty, size) => {
                    let size = self.const_eval_rvalue(size)?;
                    match size {
                        Value::USize(size) => {
                            let id = self.ir.make_id();
                            let value = make_uninitialized(self.ir, self.types.array(ty, size));
                            self.ctx.malloc_bag.define(id, value);

                            Ok(Value::Pointer(
                                LValue::Index(LValue::Alloc(id).alloc_on(self.ir), 0),
                                ty,
                            ))
                        }
                        _ => bug!(self),
                    }
                }
                IntrinsicValueKind::ConstFree(ptr) => {
                    let ptr = self.const_eval_rvalue(ptr)?;
                    match ptr {
                        // don't need to check that it's a compatible pointer here really
                        Value::Pointer(LValue::Index(LValue::Alloc(id), 0), _)
                            if self.ctx.malloc_bag.free(*id).is_some() =>
                        {
                            Ok(Value::Void)
                        }

                        _ => Err(ConstEvalErrorKind::InvalidFree).with_backtrace(&self.diag),
                    }
                }
                IntrinsicValueKind::Expect(inner, _) => self.const_eval_rvalue(inner),
            },
            ExprKind::Item(item) => match item.get() {
                Ok(Item::Function(_)) => Ok(Value::FunctionPointer(item)),
                Ok(Item::Const(_)) => Ok(Value::LValue(LValue::Const(item))),
                _ => unsupported!(self),
            },
            ExprKind::Return(value) => {
                self.return_slot = Some(self.const_eval_rvalue(value)?);
                Err(ConstEvalErrorKind::Return).with_backtrace(&self.diag)
            }
            ExprKind::Call(callee, args) => {
                let callee = self.const_eval_rvalue(callee)?;
                let (arg_spec, func_body, _ret) = match callee {
                    Value::FunctionPointer(fun) => {
                        let func = fun.get_function().with_backtrace(&self.diag)?;
                        let func_body = func
                            .body
                            .get()
                            .ok_or_else(|| {
                                ConstEvalErrorKind::UnsupportedFunction(
                                    func.name.unwrap_or("<unnamed>").to_string(),
                                )
                            })
                            .with_backtrace(&self.diag)?;

                        (func.args, func_body, func.return_type)
                    }
                    _ => unsupported!(self),
                };

                let mut remapped_variables = HashMap::default();
                for local_def in func_body.local_defs {
                    let new_id = self.ir.make_id();
                    remapped_variables.insert(local_def.id, new_id);

                    self.ctx.declare(new_id, local_def.ty);
                }

                for (arg, arg_spec) in args.iter().zip(arg_spec) {
                    let arg = self.const_eval_rvalue(arg)?;
                    let new_id = self.ir.make_id();
                    remapped_variables.insert(arg_spec.id, new_id);

                    self.ctx.define(new_id, arg);
                }

                let mut child = self.make_child(remapped_variables)?;

                let ret = match child.const_eval_rvalue(func_body.expr) {
                    Ok(value) => Ok(value),
                    Err(e) => {
                        let AluminaError::CodeErrors(ref v) = e else {
                            return Err(e);
                        };
                        let [CodeError {
                            kind: CodeDiagnostic::CannotConstEvaluate(ConstEvalErrorKind::Return),
                            ..
                        }] = v[..]
                        else {
                            return Err(e);
                        };
                        let value = child.return_slot.take().unwrap();
                        Ok(value)
                    }
                };
                ret
            }
            ExprKind::Unreachable => {
                Err(ConstEvalErrorKind::ToReachTheUnreachableStar).with_backtrace(&self.diag)
            }
            ExprKind::Tag(tag, inner) => match *tag {
                "non_const" => {
                    if self.codegen {
                        self.const_eval_rvalue(inner)
                    } else {
                        unsupported!(self)
                    }
                }
                _ => self.const_eval_rvalue(inner),
            },
        }
    }

    // Handle pointer arithmetic
    fn plus_minus(
        &mut self,
        lhs: Value<'ir>,
        lhs_ty: TyP<'ir>,
        op: BinOp,
        rhs: Value<'ir>,
        rhs_ty: TyP<'ir>,
    ) -> Result<Value<'ir>, AluminaError> {
        macro_rules! offset {
            () => {
                match rhs {
                    // if you do offsets > isize::MAX in const-eval, you are on your own
                    Value::USize(i) => i as isize,
                    Value::ISize(i) => i,
                    _ => unsupported!(self),
                }
            };
        }

        macro_rules! check_type_match {
            ($original:expr, $current:expr) => {{
                let Ty::Pointer(current, _) = $current else {
                    bug!(self);
                };

                if $original != *current {
                    return Err(ConstEvalErrorKind::IncompatiblePointer).with_backtrace(&self.diag);
                }
            }};
        }

        match (lhs, rhs) {
            (
                Value::Pointer(LValue::Index(a, a_offset), a_orig),
                Value::Pointer(LValue::Index(b, b_offset), b_orig),
            ) if op == BinOp::Minus => {
                if b != a {
                    return Err(ConstEvalErrorKind::ProvenanceMismatch).with_backtrace(&self.diag);
                }

                check_type_match!(a_orig, lhs_ty);
                check_type_match!(b_orig, rhs_ty);

                let diff = (a_offset as isize) - (b_offset as isize);
                return Ok(Value::ISize(diff));
            }
            (Value::Bytes(a, a_offset), Value::Bytes(b, b_offset)) if op == BinOp::Minus => {
                if b != a {
                    return Err(ConstEvalErrorKind::ProvenanceMismatch).with_backtrace(&self.diag);
                }

                let diff = (a_offset as isize) - (b_offset as isize);
                return Ok(Value::ISize(diff));
            }
            (Value::Pointer(a, a_orig), Value::Pointer(b, b_orig)) if op == BinOp::Minus => {
                if a == b {
                    check_type_match!(a_orig, lhs_ty);
                    check_type_match!(b_orig, rhs_ty);

                    return Ok(Value::ISize(0));
                } else {
                    return Err(ConstEvalErrorKind::ProvenanceMismatch).with_backtrace(&self.diag);
                }
            }
            (Value::Bytes(buf, offset), _) => {
                let new_offset = match op {
                    BinOp::Plus => (offset as isize) + offset!(),
                    BinOp::Minus => (offset as isize) - offset!(),
                    _ => bug!(self),
                };
                if new_offset < 0 || new_offset > (buf.len() as isize) {
                    return Err(ConstEvalErrorKind::IndexOutOfBounds).with_backtrace(&self.diag);
                }
                return Ok(Value::Bytes(buf, new_offset as usize));
            }
            (Value::Pointer(LValue::Index(inner, offset), orig), _) => {
                let arr = match self.materialize_lvalue(*inner)? {
                    Value::Array(arr) => arr,
                    _ => unsupported!(self),
                };

                check_type_match!(orig, lhs_ty);

                let new_offset = match op {
                    BinOp::Plus => (offset as isize) + offset!(),
                    BinOp::Minus => (offset as isize) - offset!(),
                    _ => bug!(self),
                };
                if new_offset < 0 || new_offset > (arr.len() as isize) {
                    return Err(ConstEvalErrorKind::IndexOutOfBounds).with_backtrace(&self.diag);
                }
                return Ok(Value::Pointer(
                    LValue::Index(inner, new_offset as usize),
                    orig,
                ));
            }

            _ => {}
        }

        let ret = match op {
            BinOp::Plus => lhs + rhs,
            BinOp::Minus => lhs - rhs,
            _ => unreachable!(),
        };

        ret.with_backtrace(&self.diag)
    }

    fn bin_op(
        &mut self,
        lhs: Value<'ir>,
        lhs_ty: TyP<'ir>,
        op: BinOp,
        rhs: Value<'ir>,
        rhs_ty: TyP<'ir>,
    ) -> Result<Value<'ir>, AluminaError> {
        let ret = match op {
            BinOp::BitAnd => lhs & rhs,
            BinOp::BitOr => lhs | rhs,
            BinOp::BitXor => lhs ^ rhs,
            BinOp::Or => lhs | rhs,
            BinOp::And => lhs & rhs,
            BinOp::Eq => lhs.equals(rhs),
            BinOp::Neq => lhs.equals(rhs).and_then(|v| !v),
            BinOp::Lt => Ok(Value::Bool(matches!(
                lhs.compare(rhs).with_backtrace(&self.diag)?,
                Some(Ordering::Less)
            ))),
            BinOp::LEq => Ok(Value::Bool(matches!(
                lhs.compare(rhs).with_backtrace(&self.diag)?,
                Some(Ordering::Less | Ordering::Equal)
            ))),
            BinOp::Gt => Ok(Value::Bool(matches!(
                lhs.compare(rhs).with_backtrace(&self.diag)?,
                Some(Ordering::Greater)
            ))),
            BinOp::GEq => Ok(Value::Bool(matches!(
                lhs.compare(rhs).with_backtrace(&self.diag)?,
                Some(Ordering::Greater | Ordering::Equal)
            ))),
            BinOp::LShift => lhs << rhs,
            BinOp::RShift => lhs >> rhs,
            BinOp::Mul => lhs * rhs,
            BinOp::Div => lhs / rhs,
            BinOp::Mod => lhs % rhs,
            BinOp::Plus | BinOp::Minus => return self.plus_minus(lhs, lhs_ty, op, rhs, rhs_ty),
        };

        ret.with_backtrace(&self.diag)
    }

    pub fn extract_constant_string_from_slice(&mut self, value: &Value<'ir>) -> Option<&'ir [u8]> {
        match value {
            Value::Struct(fields) => {
                let mut buf = None;
                let mut len = None;
                for (_id, value) in fields.iter() {
                    match value {
                        Value::USize(len_) => {
                            len = Some(*len_);
                        }
                        Value::Bytes(r, offset) => {
                            buf = r.get(*offset..);
                        }
                        Value::Pointer(LValue::Index(r, offset), _) => {
                            let r = self.materialize_lvalue(**r).unwrap();
                            if let Value::Array(elems) = r {
                                let mut bytes = Vec::with_capacity(elems.len());
                                for elem in elems.iter().skip(*offset) {
                                    if let Value::U8(byte) = elem {
                                        bytes.push(*byte);
                                    } else {
                                        // Uninitialized bytes are zero?
                                        bytes.push(0);
                                    }
                                }
                                buf = Some(self.ir.arena.alloc_slice_copy(&bytes[..]));
                            }
                        }
                        _ => return None,
                    }
                }

                if let (Some(buf), Some(len)) = (buf, len) {
                    buf.get(..len)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

fn check_lvalue_leak(value: &Value<'_>) -> Result<(), ConstEvalErrorKind> {
    match value {
        Value::Pointer(lvalue, _) | Value::LValue(lvalue) => check_lvalue_leak_lvalue(lvalue),
        Value::Tuple(values) => values.iter().try_for_each(check_lvalue_leak),
        Value::Struct(fields) => fields
            .iter()
            .map(|(_, v)| v)
            .try_for_each(check_lvalue_leak),
        Value::Array(values) => values.iter().try_for_each(check_lvalue_leak),
        _ => Ok(()),
    }
}

fn check_lvalue_leak_lvalue(value: &LValue<'_>) -> Result<(), ConstEvalErrorKind> {
    match value {
        LValue::Const(_) => Ok(()),
        LValue::Alloc(_) => Err(ConstEvalErrorKind::LValueLeak),
        LValue::Variable(_) => Err(ConstEvalErrorKind::LValueLeak),
        LValue::Field(inner, _) | LValue::Index(inner, _) | LValue::TupleIndex(inner, _) => {
            check_lvalue_leak_lvalue(inner)
        }
    }
}

fn make_uninitialized<'ir>(ir: &'ir IrCtx<'ir>, ty: TyP<'ir>) -> Value<'ir> {
    match ty {
        Ty::Array(inner, size) => {
            let inner = make_uninitialized(ir, inner);
            let buf = ir.arena.alloc_slice_fill_copy(*size, inner);

            Value::Array(buf)
        }
        Ty::Tuple(tys) => {
            let elems = tys.iter().map(|t| make_uninitialized(ir, t));

            Value::Tuple(ir.arena.alloc_slice_fill_iter(elems))
        }
        Ty::Item(item) => match item.get().unwrap() {
            Item::StructLike(s) => {
                let fields = s.fields.iter().map(|f| {
                    let value = make_uninitialized(ir, f.ty);
                    (f.id, value)
                });

                Value::Struct(ir.arena.alloc_slice_fill_iter(fields))
            }
            Item::Function(_) => Value::FunctionPointer(item),
            _ => Value::Uninitialized,
        },
        _ => Value::Uninitialized,
    }
}

pub fn make_zeroed<'ir>(ir: &'ir IrCtx<'ir>, ty: TyP<'ir>) -> Value<'ir> {
    match ty {
        Ty::Array(inner, size) => {
            let inner = make_zeroed(ir, inner);
            let buf = ir.arena.alloc_slice_fill_copy(*size, inner);

            Value::Array(buf)
        }
        Ty::Tuple(tys) => {
            let elems = tys.iter().map(|t| make_zeroed(ir, t));

            Value::Tuple(ir.arena.alloc_slice_fill_iter(elems))
        }
        Ty::Item(item) => match item.get().unwrap() {
            Item::StructLike(s) => {
                let fields = s.fields.iter().map(|f| {
                    let value = make_zeroed(ir, f.ty);
                    (f.id, value)
                });

                Value::Struct(ir.arena.alloc_slice_fill_iter(fields))
            }
            Item::Enum(e) => make_zeroed(ir, e.underlying_ty),
            Item::Closure(c) => {
                let fields = c.data.fields.iter().map(|f| (f.id, make_zeroed(ir, f.ty)));

                Value::Struct(ir.arena.alloc_slice_fill_iter(fields))
            }
            _ => Value::Uninitialized,
        },
        Ty::Pointer(_, _) | Ty::FunctionPointer(_, _) => Value::USize(0),
        Ty::Builtin(kind) => match kind {
            BuiltinType::Never => Value::Uninitialized,
            BuiltinType::Bool => Value::Bool(false),
            BuiltinType::U8 => Value::U8(0),
            BuiltinType::U16 => Value::U16(0),
            BuiltinType::U32 => Value::U32(0),
            BuiltinType::U64 => Value::U64(0),
            BuiltinType::U128 => Value::U128(0),
            BuiltinType::USize => Value::USize(0),
            BuiltinType::ISize => Value::ISize(0),
            BuiltinType::I8 => Value::I8(0),
            BuiltinType::I16 => Value::I16(0),
            BuiltinType::I32 => Value::I32(0),
            BuiltinType::I64 => Value::I64(0),
            BuiltinType::I128 => Value::I128(0),

            // All 0 bit patterns are valid for floats (representing +0.0)
            BuiltinType::F32 => Value::F32(0.0),
            BuiltinType::F64 => Value::F64(0.0),
        },
    }
}
