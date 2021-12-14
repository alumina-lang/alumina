/// Const evaluation at the moment is very rudimentary and is there only to support the
/// use case where enum members underlyng values are expressed as bitwise operations, as
/// is commonly the case.
use crate::ast::BinOp;
use std::{
    cmp::Ordering,
    fmt::{Display, Error, Formatter},
    num::Wrapping,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub},
};

use super::{BuiltinType, ExprKind, ExprP, Lit, Ty, UnOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Hash)]
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
    Str(&'ir [u8]),
}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Value::Void => write!(f, "void"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::U8(b) => write!(f, "{}", b),
            Value::U16(b) => write!(f, "{}", b),
            Value::U32(b) => write!(f, "{}", b),
            Value::U64(b) => write!(f, "{}", b),
            Value::U128(b) => write!(f, "{}", b),
            Value::I8(b) => write!(f, "{}", b),
            Value::I16(b) => write!(f, "{}", b),
            Value::I32(b) => write!(f, "{}", b),
            Value::I64(b) => write!(f, "{}", b),
            Value::I128(b) => write!(f, "{}", b),
            Value::USize(b) => write!(f, "{}", b),
            Value::ISize(_) => todo!(),
            Value::Str(s) => {
                let as_str = std::str::from_utf8(s).map_err(|_| Error)?;
                write!(f, "{}", as_str)?;
                Ok(())
            }
        }
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

pub(crate) use numeric_of_kind;

impl<'ir> Value<'ir> {
    pub fn type_kind(&self) -> Option<BuiltinType> {
        match self {
            Value::Void => Some(BuiltinType::Void),
            Value::Bool(_) => Some(BuiltinType::Bool),
            Value::U8(_) => Some(BuiltinType::U8),
            Value::U16(_) => Some(BuiltinType::U16),
            Value::U32(_) => Some(BuiltinType::U32),
            Value::U64(_) => Some(BuiltinType::U64),
            Value::U128(_) => Some(BuiltinType::U128),
            Value::I8(_) => Some(BuiltinType::I8),
            Value::I16(_) => Some(BuiltinType::I16),
            Value::I32(_) => Some(BuiltinType::I32),
            Value::I64(_) => Some(BuiltinType::I64),
            Value::I128(_) => Some(BuiltinType::I128),
            Value::USize(_) => Some(BuiltinType::USize),
            Value::ISize(_) => Some(BuiltinType::ISize),
            _ => None,
        }
    }

    fn equal(self, other: Value) -> Result<Value<'ir>, ()> {
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
            _ => Err(()),
        }
    }

    fn cmp(self, other: Value) -> Result<Ordering, ()> {
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
            _ => Err(()),
        }
    }
}

impl<'ir> Add for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn add(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8((Wrapping(a) + Wrapping(b)).0)),
            (U16(a), U16(b)) => Ok(U16((Wrapping(a) + Wrapping(b)).0)),
            (U32(a), U32(b)) => Ok(U32((Wrapping(a) + Wrapping(b)).0)),
            (U64(a), U64(b)) => Ok(U64((Wrapping(a) + Wrapping(b)).0)),
            (U128(a), U128(b)) => Ok(U128((Wrapping(a) + Wrapping(b)).0)),
            (I8(a), I8(b)) => Ok(I8((Wrapping(a) + Wrapping(b)).0)),
            (I16(a), I16(b)) => Ok(I16((Wrapping(a) + Wrapping(b)).0)),
            (I32(a), I32(b)) => Ok(I32((Wrapping(a) + Wrapping(b)).0)),
            (I64(a), I64(b)) => Ok(I64((Wrapping(a) + Wrapping(b)).0)),
            (I128(a), I128(b)) => Ok(I128((Wrapping(a) + Wrapping(b)).0)),
            (USize(a), USize(b)) => Ok(USize((Wrapping(a) + Wrapping(b)).0)),
            (ISize(a), ISize(b)) => Ok(ISize((Wrapping(a) + Wrapping(b)).0)),
            _ => Err(()),
        }
    }
}

impl<'ir> Sub for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn sub(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8((Wrapping(a) - Wrapping(b)).0)),
            (U16(a), U16(b)) => Ok(U16((Wrapping(a) - Wrapping(b)).0)),
            (U32(a), U32(b)) => Ok(U32((Wrapping(a) - Wrapping(b)).0)),
            (U64(a), U64(b)) => Ok(U64((Wrapping(a) - Wrapping(b)).0)),
            (U128(a), U128(b)) => Ok(U128((Wrapping(a) - Wrapping(b)).0)),
            (I8(a), I8(b)) => Ok(I8((Wrapping(a) - Wrapping(b)).0)),
            (I16(a), I16(b)) => Ok(I16((Wrapping(a) - Wrapping(b)).0)),
            (I32(a), I32(b)) => Ok(I32((Wrapping(a) - Wrapping(b)).0)),
            (I64(a), I64(b)) => Ok(I64((Wrapping(a) - Wrapping(b)).0)),
            (I128(a), I128(b)) => Ok(I128((Wrapping(a) - Wrapping(b)).0)),
            (USize(a), USize(b)) => Ok(USize((Wrapping(a) - Wrapping(b)).0)),
            (ISize(a), ISize(b)) => Ok(ISize((Wrapping(a) - Wrapping(b)).0)),
            _ => Err(()),
        }
    }
}

impl<'ir> Mul for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn mul(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        match (self, other) {
            (U8(a), U8(b)) => Ok(U8((Wrapping(a) * Wrapping(b)).0)),
            (U16(a), U16(b)) => Ok(U16((Wrapping(a) * Wrapping(b)).0)),
            (U32(a), U32(b)) => Ok(U32((Wrapping(a) * Wrapping(b)).0)),
            (U64(a), U64(b)) => Ok(U64((Wrapping(a) * Wrapping(b)).0)),
            (U128(a), U128(b)) => Ok(U128((Wrapping(a) * Wrapping(b)).0)),
            (I8(a), I8(b)) => Ok(I8((Wrapping(a) * Wrapping(b)).0)),
            (I16(a), I16(b)) => Ok(I16((Wrapping(a) * Wrapping(b)).0)),
            (I32(a), I32(b)) => Ok(I32((Wrapping(a) * Wrapping(b)).0)),
            (I64(a), I64(b)) => Ok(I64((Wrapping(a) * Wrapping(b)).0)),
            (I128(a), I128(b)) => Ok(I128((Wrapping(a) * Wrapping(b)).0)),
            (USize(a), USize(b)) => Ok(USize((Wrapping(a) * Wrapping(b)).0)),
            (ISize(a), ISize(b)) => Ok(ISize((Wrapping(a) * Wrapping(b)).0)),
            _ => Err(()),
        }
    }
}

impl<'ir> Shl<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn shl(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        let other = match other {
            USize(a) => a,
            _ => return Err(()),
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
            _ => Err(()),
        }
    }
}

impl<'ir> Neg for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn neg(self) -> Result<Value<'ir>, ()> {
        use Value::*;

        match self {
            I8(a) => Ok(I8(-a)),
            I16(a) => Ok(I16(-a)),
            I32(a) => Ok(I32(-a)),
            I64(a) => Ok(I64(-a)),
            I128(a) => Ok(I128(-a)),
            ISize(a) => Ok(ISize(-a)),
            _ => Err(()),
        }
    }
}

impl<'ir> Not for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn not(self) -> Result<Value<'ir>, ()> {
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
            _ => Err(()),
        }
    }
}

impl<'ir> Shr<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn shr(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        let other = match other {
            USize(a) => a,
            _ => return Err(()),
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
            _ => Err(()),
        }
    }
}

impl<'ir> BitOr for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn bitor(self, other: Value) -> Result<Value<'ir>, ()> {
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
            _ => Err(()),
        }
    }
}

impl<'ir> BitXor for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn bitxor(self, other: Value) -> Result<Value<'ir>, ()> {
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
            _ => Err(()),
        }
    }
}

impl<'ir> BitAnd for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn bitand(self, other: Value) -> Result<Value<'ir>, ()> {
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
            _ => Err(()),
        }
    }
}

impl<'ir> Div for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn div(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        let result = match (self, other) {
            (U8(a), U8(b)) => a.checked_div(b).map(|v| U8(v)),
            (U16(a), U16(b)) => a.checked_div(b).map(|v| U16(v)),
            (U32(a), U32(b)) => a.checked_div(b).map(|v| U32(v)),
            (U64(a), U64(b)) => a.checked_div(b).map(|v| U64(v)),
            (U128(a), U128(b)) => a.checked_div(b).map(|v| U128(v)),
            (I8(a), I8(b)) => a.checked_div(b).map(|v| I8(v)),
            (I16(a), I16(b)) => a.checked_div(b).map(|v| I16(v)),
            (I32(a), I32(b)) => a.checked_div(b).map(|v| I32(v)),
            (I64(a), I64(b)) => a.checked_div(b).map(|v| I64(v)),
            (I128(a), I128(b)) => a.checked_div(b).map(|v| I128(v)),
            (USize(a), USize(b)) => a.checked_div(b).map(|v| USize(v)),
            (ISize(a), ISize(b)) => a.checked_div(b).map(|v| ISize(v)),
            _ => None,
        };

        result.ok_or(())
    }
}

impl<'ir> Rem for Value<'ir> {
    type Output = Result<Value<'ir>, ()>;
    fn rem(self, other: Value) -> Result<Value<'ir>, ()> {
        use Value::*;

        let result = match (self, other) {
            (U8(a), U8(b)) => a.checked_rem(b).map(|v| U8(v)),
            (U16(a), U16(b)) => a.checked_rem(b).map(|v| U16(v)),
            (U32(a), U32(b)) => a.checked_rem(b).map(|v| U32(v)),
            (U64(a), U64(b)) => a.checked_rem(b).map(|v| U64(v)),
            (U128(a), U128(b)) => a.checked_rem(b).map(|v| U128(v)),
            (I8(a), I8(b)) => a.checked_rem(b).map(|v| I8(v)),
            (I16(a), I16(b)) => a.checked_rem(b).map(|v| I16(v)),
            (I32(a), I32(b)) => a.checked_rem(b).map(|v| I32(v)),
            (I64(a), I64(b)) => a.checked_rem(b).map(|v| I64(v)),
            (I128(a), I128(b)) => a.checked_rem(b).map(|v| I128(v)),
            (USize(a), USize(b)) => a.checked_rem(b).map(|v| USize(v)),
            (ISize(a), ISize(b)) => a.checked_rem(b).map(|v| ISize(v)),
            _ => None,
        };

        result.ok_or(())
    }
}

pub fn const_eval<'ast, 'ir>(expr: ExprP<'ir>) -> Result<Value<'ir>, ()> {
    match &expr.kind {
        ExprKind::Void => Ok(Value::Void),
        ExprKind::Binary(op, lhs, rhs) => {
            let lhs = const_eval(lhs)?;
            let rhs = const_eval(rhs)?;

            match op {
                BinOp::And => match (lhs, rhs) {
                    (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a && b)),
                    _ => Err(()),
                },
                BinOp::Or => match (lhs, rhs) {
                    (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a || b)),
                    _ => Err(()),
                },
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
            }
        }
        ExprKind::Unary(op, inner) => {
            let inner = const_eval(inner)?;

            match op {
                UnOp::Not if matches!(inner, Value::Bool(_)) => !inner,
                UnOp::Neg => -inner,
                UnOp::BitNot if !matches!(inner, Value::Bool(_)) => !inner,
                _ => Err(()),
            }
        }
        ExprKind::ConstValue(value) => Ok(*value),
        ExprKind::Lit(l) => match l {
            Lit::Bool(b) => Ok(Value::Bool(*b)),
            Lit::Int(i) => match expr.ty {
                Ty::Builtin(BuiltinType::U8) => Ok(Value::U8(*i as u8)),
                Ty::Builtin(BuiltinType::U16) => Ok(Value::U16(*i as u16)),
                Ty::Builtin(BuiltinType::U32) => Ok(Value::U32(*i as u32)),
                Ty::Builtin(BuiltinType::U64) => Ok(Value::U64(*i as u64)),
                Ty::Builtin(BuiltinType::U128) => Ok(Value::U128(*i as u128)),
                Ty::Builtin(BuiltinType::I8) => Ok(Value::I8(*i as i8)),
                Ty::Builtin(BuiltinType::I16) => Ok(Value::I16(*i as i16)),
                Ty::Builtin(BuiltinType::I32) => Ok(Value::I32(*i as i32)),
                Ty::Builtin(BuiltinType::I64) => Ok(Value::I64(*i as i64)),
                Ty::Builtin(BuiltinType::I128) => Ok(Value::I128(*i as i128)),
                Ty::Builtin(BuiltinType::USize) => Ok(Value::USize(*i as usize)),
                Ty::Builtin(BuiltinType::ISize) => Ok(Value::ISize(*i as isize)),
                _ => unreachable!(),
            },
            Lit::Str(s) => Ok(Value::Str(*s)),
            _ => Err(()),
        },
        _ => Err(()),
    }
}
