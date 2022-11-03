/// An interpreter for constant expressions. It's quite slow.
use crate::ast::BinOp;
use crate::common::{ArenaAllocatable, HashMap, Marker};
use crate::intrinsics::IntrinsicValueKind;
use crate::ir::{BuiltinType, ExprKind, ExprP, IRItem, IrCtx, IrId, Statement, Ty, TyP, UnOp};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::num::TryFromIntError;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};
use std::rc::Rc;

use thiserror::Error;

const MAX_RECURSION_DEPTH: usize = 100;
const MAX_ITERATIONS: usize = 10000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    F32(&'ir str),
    F64(&'ir str),
    Str(&'ir [u8], usize),
    Tuple(&'ir [Value<'ir>]),
    Array(&'ir [Value<'ir>]),
    Struct(&'ir [(IrId, Value<'ir>)]),
    FunctionPointer(super::IRItemP<'ir>),
    Pointer(LValue<'ir>),
    LValue(LValue<'ir>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LValue<'ir> {
    Variable(IrId),
    Field(&'ir LValue<'ir>, IrId),
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
    CompilerBug,
    #[error("cyclic reference")]
    CyclicReference,
    #[error("trying to access uninitialized value")]
    Uninitialized,
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

    // These are not errors, but they are used to signal that the evaluation should stop.
    // They are bugs if they leak to the caller
    #[error("ice: non-local jump")]
    Jump(IrId),
    #[error("ice: return from a constant expression")]
    Return,
}

#[derive(Debug, Error, Clone, Hash, PartialEq, Eq)]
#[error("{}", .kind)]
pub struct ConstEvalError {
    pub kind: ConstEvalErrorKind,
    pub backtrace: Vec<Marker>,
}

impl From<ConstEvalErrorKind> for ConstEvalError {
    fn from(kind: ConstEvalErrorKind) -> Self {
        Self {
            kind,
            backtrace: Vec::new(),
        }
    }
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I16(a), I16(b)) => a
                .checked_add(b)
                .map(I16)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I32(a), I32(b)) => a
                .checked_add(b)
                .map(I32)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I64(a), I64(b)) => a
                .checked_add(b)
                .map(I64)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I128(a), I128(b)) => a
                .checked_add(b)
                .map(I128)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (ISize(a), ISize(b)) => a
                .checked_add(b)
                .map(ISize)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I16(a), I16(b)) => a
                .checked_sub(b)
                .map(I16)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I32(a), I32(b)) => a
                .checked_sub(b)
                .map(I32)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I64(a), I64(b)) => a
                .checked_sub(b)
                .map(I64)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I128(a), I128(b)) => a
                .checked_sub(b)
                .map(I128)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (ISize(a), ISize(b)) => a
                .checked_sub(b)
                .map(ISize)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I16(a), I16(b)) => a
                .checked_mul(b)
                .map(I16)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I32(a), I32(b)) => a
                .checked_mul(b)
                .map(I32)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I64(a), I64(b)) => a
                .checked_mul(b)
                .map(I64)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (I128(a), I128(b)) => a
                .checked_mul(b)
                .map(I128)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            (ISize(a), ISize(b)) => a
                .checked_mul(b)
                .map(ISize)
                .ok_or_else(|| ConstEvalErrorKind::ArithmeticOverflow.into()),
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
        }
    }
}

impl<'ir> Shl<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn shl(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        let other: std::result::Result<usize, TryFromIntError> = match other {
            U8(other) => Ok(other as _),
            U16(other) => Ok(other as _),
            U32(other) => other.try_into(),
            U64(other) => other.try_into(),
            U128(other) => other.try_into(),
            USize(other) => Ok(other),
            I8(other) => other.try_into(),
            I16(other) => other.try_into(),
            I32(other) => other.try_into(),
            I64(other) => other.try_into(),
            I128(other) => other.try_into(),
            ISize(other) => other.try_into(),
            _ => return Err(ConstEvalErrorKind::CompilerBug.into()),
        };
        let other = other.map_err(|_| ConstEvalErrorKind::ArithmeticOverflow)?;

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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
        }
    }
}

impl<'ir> Shr<Value<'ir>> for Value<'ir> {
    type Output = Result<Value<'ir>>;
    fn shr(self, other: Value) -> Result<Value<'ir>> {
        use Value::*;

        let other: std::result::Result<usize, TryFromIntError> = match other {
            U8(other) => Ok(other as _),
            U16(other) => Ok(other as _),
            U32(other) => other.try_into(),
            U64(other) => other.try_into(),
            U128(other) => other.try_into(),
            USize(other) => Ok(other),
            I8(other) => other.try_into(),
            I16(other) => other.try_into(),
            I32(other) => other.try_into(),
            I64(other) => other.try_into(),
            I128(other) => other.try_into(),
            ISize(other) => other.try_into(),
            _ => return Err(ConstEvalErrorKind::CompilerBug.into()),
        };
        let other = other.map_err(|_| ConstEvalErrorKind::ArithmeticOverflow)?;

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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
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

        result.ok_or_else(|| ConstEvalErrorKind::DivisionByZero.into())
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

        result.ok_or_else(|| ConstEvalErrorKind::DivisionByZero.into())
    }
}

struct ConstEvalCtxInner<'ir> {
    variables: HashMap<IrId, Value<'ir>>,
    steps_remaining: usize,
}

#[derive(Clone)]
pub struct ConstEvalCtx<'ir> {
    ir: &'ir IrCtx<'ir>,
    inner: Rc<RefCell<ConstEvalCtxInner<'ir>>>,
}

impl<'ir> ConstEvalCtx<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            inner: Rc::new(RefCell::new(ConstEvalCtxInner {
                variables: HashMap::default(),
                steps_remaining: MAX_ITERATIONS,
            })),
        }
    }

    pub fn step(&self) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        if inner.steps_remaining == 0 {
            return Err(ConstEvalErrorKind::TooManyIterations.into());
        }
        inner.steps_remaining -= 1;
        Ok(())
    }

    pub fn define(&self, id: IrId, value: Value<'ir>) {
        self.inner.borrow_mut().variables.insert(id, value);
    }

    pub fn declare(&self, id: IrId, typ: TyP<'ir>) {
        self.inner
            .borrow_mut()
            .variables
            .insert(id, make_uninitialized(self.ir, typ));
    }

    pub fn assign(&self, id: IrId, value: Value<'ir>) {
        self.inner.borrow_mut().variables.insert(id, value);
    }

    pub fn load_var(&self, id: IrId) -> Value<'ir> {
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
    remapped_variables: HashMap<IrId, IrId>,
}

impl<'ir> ConstEvaluator<'ir> {
    pub fn new<I>(ir: &'ir IrCtx<'ir>, local_types: I) -> Self
    where
        I: IntoIterator<Item = (IrId, TyP<'ir>)>,
    {
        let ctx = ConstEvalCtx::new(ir);
        for (id, typ) in local_types {
            ctx.declare(id, typ);
        }

        Self {
            ir,
            return_slot: None,
            remaining_depth: MAX_RECURSION_DEPTH,
            remapped_variables: Default::default(),
            ctx,
        }
    }

    fn make_child(&self, remapped_variables: HashMap<IrId, IrId>) -> Result<Self> {
        Ok(Self {
            ir: self.ir,
            ctx: self.ctx.clone(),
            return_slot: None,
            remaining_depth: self
                .remaining_depth
                .checked_sub(1)
                .ok_or(ConstEvalErrorKind::TooDeep)?,
            remapped_variables,
        })
    }

    fn cast(&mut self, inner: ExprP<'ir>, mut target: TyP<'ir>) -> Result<Value<'ir>> {
        let val = self.const_eval_rvalue(inner)?;
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
            Value::Bool(a) => Value::U128(a as u128),
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
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
        }
    }

    fn field(&mut self, r#struct: Value<'ir>, field: IrId) -> Result<Value<'ir>> {
        match r#struct {
            Value::LValue(lv) => Ok(Value::LValue(LValue::Field(lv.alloc_on(self.ir), field))),
            Value::Struct(fields) => Ok(fields
                .iter()
                .find(|(f, _)| *f == field)
                .map(|(_, v)| *v)
                .unwrap_or(Value::Uninitialized)),
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
        }
    }

    fn index(&mut self, array: Value<'ir>, idx: usize) -> Result<Value<'ir>> {
        match array {
            Value::LValue(lv) => Ok(Value::LValue(LValue::Index(lv.alloc_on(self.ir), idx))),
            Value::Array(values) => values
                .get(idx)
                .copied()
                .ok_or_else(|| ConstEvalErrorKind::IndexOutOfBounds.into()),
            _ => Err(ConstEvalErrorKind::Unsupported.into()),
        }
    }

    fn tuple_index(&mut self, tup: Value<'ir>, idx: usize) -> Result<Value<'ir>> {
        match tup {
            Value::LValue(lv) => Ok(Value::LValue(LValue::TupleIndex(lv.alloc_on(self.ir), idx))),
            Value::Tuple(values) => Ok(values.get(idx).cloned().unwrap_or(Value::Uninitialized)),
            _ => Err(ConstEvalErrorKind::CompilerBug.into()),
        }
    }

    pub fn const_eval(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>> {
        // public facing interface. we clean up things that should not appear in the IR
        let ret = self.const_eval_rvalue(expr)?;
        check_lvalue_leak(&ret)?;
        Ok(ret)
    }

    fn materialize(&mut self, value: Value<'ir>) -> Result<Value<'ir>> {
        match value {
            Value::LValue(v) => self.materialize_lvalue(v),
            _ => Ok(value),
        }
    }

    fn const_eval_rvalue(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>> {
        self.const_eval_defered(expr)
            .and_then(|v| self.materialize(v))
    }

    fn eval_statements(&mut self, statements: &[Statement<'ir>]) -> Result<()> {
        let label_indexes: HashMap<IrId, usize> = statements
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
                        Err(ConstEvalError {
                            kind: ConstEvalErrorKind::Jump(label),
                            ..
                        }) => {
                            if let Some(new_ip) = label_indexes.get(&label) {
                                ip = *new_ip;
                                continue;
                            } else {
                                // Go up one level
                                return Err(ConstEvalErrorKind::Jump(label).into());
                            }
                        }
                        Err(e) => return Err(e),
                    }
                }
                Statement::Label(_) => {}
            }
            ip += 1;
        }

        Ok(())
    }

    fn materialize_lvalue(&mut self, value: LValue<'ir>) -> Result<Value<'ir>> {
        match value {
            LValue::Variable(id) => Ok(self.ctx.load_var(id)),
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

    fn assign(&mut self, lhs: LValue<'ir>, value: Value<'ir>) -> Result<()> {
        match lhs {
            LValue::Variable(id) => {
                self.ctx.assign(id, value);
                Ok(())
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
                    _ => Err(ConstEvalErrorKind::CompilerBug.into()),
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
                    _ => Err(ConstEvalErrorKind::CompilerBug.into()),
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
                    _ => Err(ConstEvalErrorKind::CompilerBug.into()),
                }
            }
        }
    }

    #[allow(unreachable_code)]
    fn const_eval_defered(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>> {
        // Comment this line to debug expressions not being evaluated
        // successfully
        return self.const_eval_defered_inner(expr);

        match self.const_eval_defered_inner(expr) {
            Ok(v) => Ok(v),
            Err(ref err @ ConstEvalError { ref kind, .. })
                if !matches!(
                    kind,
                    ConstEvalErrorKind::Jump(..) | ConstEvalErrorKind::Return
                ) =>
            {
                panic!(
                    "Could not const-evaluate: {}\nEXPRESSION:\n{:#?}",
                    err, expr
                )
            }
            Err(e) => Err(e),
        }
    }

    /// Variant of const-eval that leaves LValues in place
    fn const_eval_defered_inner(&mut self, expr: ExprP<'ir>) -> Result<Value<'ir>> {
        self.ctx.step()?;

        match &expr.kind {
            ExprKind::Void => Ok(Value::Void),
            ExprKind::Binary(op, lhs, rhs) => {
                let lhs = self.const_eval_rvalue(lhs)?;

                // Special case for short-circuiting operators
                match (op, lhs) {
                    (BinOp::Or, Value::Bool(a)) => {
                        return if a {
                            Ok(lhs)
                        } else {
                            self.const_eval_rvalue(rhs)
                        }
                    }
                    (BinOp::And, Value::Bool(a)) => {
                        return if a {
                            self.const_eval_rvalue(rhs)
                        } else {
                            Ok(lhs)
                        }
                    }
                    (BinOp::Or | BinOp::And, _) => {
                        return Err(ConstEvalErrorKind::CompilerBug.into())
                    }
                    _ => {}
                };

                let rhs = self.const_eval_rvalue(rhs)?;
                self.bin_op(lhs, *op, rhs)
            }
            ExprKind::Local(id) => Ok(Value::LValue(LValue::Variable(
                *self.remapped_variables.get(id).unwrap_or(id),
            ))),
            ExprKind::Unary(op, inner) => {
                let inner = self.const_eval_rvalue(inner)?;

                match op {
                    UnOp::Not if matches!(inner, Value::Bool(_)) => !inner,
                    UnOp::Neg => -inner,
                    UnOp::BitNot if !matches!(inner, Value::Bool(_)) => !inner,
                    _ => Err(ConstEvalErrorKind::CompilerBug.into()),
                }
            }
            ExprKind::Ref(value) => {
                let value = self.const_eval_defered(value)?;
                match value {
                    Value::LValue(lvalue) => Ok(Value::Pointer(lvalue)),
                    _ => Err(ConstEvalErrorKind::Unsupported.into()),
                }
            }
            ExprKind::Deref(value) => {
                let value = self.const_eval_rvalue(value)?;
                match value {
                    Value::Pointer(lvalue) => Ok(Value::LValue(lvalue)),
                    _ => Err(ConstEvalErrorKind::Unsupported.into()),
                }
            }
            ExprKind::Literal(value) => Ok(*value),
            ExprKind::Const(item) => item
                .get_const()
                .map(|c| c.value)
                .map_err(|_| ConstEvalErrorKind::CompilerBug.into()),
            ExprKind::Cast(inner) => self.cast(inner, expr.ty),
            ExprKind::If(cond, then, els) => {
                let condv = self.const_eval_rvalue(cond)?;

                let cond_value = match condv {
                    Value::Bool(b) => b,
                    _ => return Err(ConstEvalErrorKind::CompilerBug.into()),
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
                Ok(Value::Tuple(
                    self.ir.arena.alloc_slice_fill_iter(values.into_iter()),
                ))
            }
            ExprKind::Array(elems) => {
                let mut values = Vec::new();
                for elem in *elems {
                    values.push(self.const_eval_rvalue(elem)?);
                }
                Ok(Value::Array(
                    self.ir.arena.alloc_slice_fill_iter(values.into_iter()),
                ))
            }
            ExprKind::Goto(id) => Err(ConstEvalErrorKind::Jump(*id).into()),
            ExprKind::Struct(fields) => {
                // Last assignment wins
                let mut values = HashMap::default();
                for field in *fields {
                    values.insert(field.field, self.const_eval_rvalue(field.value)?);
                }
                Ok(Value::Struct(
                    self.ir.arena.alloc_slice_fill_iter(values.into_iter()),
                ))
            }
            ExprKind::TupleIndex(tup, idx) => {
                let tup = self.const_eval_defered(tup)?;
                self.tuple_index(tup, *idx)
            }
            ExprKind::Index(array, idx) => {
                let array = self.const_eval_defered(array)?;
                let idx = match self.const_eval_rvalue(idx)? {
                    Value::USize(idx) => idx,
                    _ => return Err(ConstEvalErrorKind::CompilerBug.into()),
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
                    _ => Err(ConstEvalErrorKind::CompilerBug.into()),
                }
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                let lhs = self.const_eval_defered(lhs)?;
                let rhs = self.const_eval_rvalue(rhs)?;
                match lhs {
                    Value::LValue(lvalue) => {
                        let normalized = self.materialize(lhs)?;
                        let res = self.bin_op(normalized, *op, rhs)?;
                        self.assign(lvalue, res)?;
                        Ok(Value::Void)
                    }
                    _ => Err(ConstEvalErrorKind::CompilerBug.into()),
                }
            }
            ExprKind::Block(statements, ret) => {
                self.eval_statements(statements)?;
                self.const_eval_rvalue(ret)
            }
            ExprKind::Intrinsic(kind) => match kind {
                IntrinsicValueKind::Uninitialized => Ok(Value::Uninitialized),
                IntrinsicValueKind::Dangling(..) => Ok(Value::Uninitialized),
                IntrinsicValueKind::SizeOfLike(_, _) => Err(ConstEvalErrorKind::Unsupported.into()),
                IntrinsicValueKind::Asm(_) => Err(ConstEvalErrorKind::Unsupported.into()),
                IntrinsicValueKind::FunctionLike(_) => Err(ConstEvalErrorKind::Unsupported.into()),
                IntrinsicValueKind::ConstLike(_) => Err(ConstEvalErrorKind::Unsupported.into()),
                IntrinsicValueKind::InConstContext => Ok(Value::Bool(true)),
            },
            ExprKind::Fn(item) => Ok(Value::FunctionPointer(item)),
            ExprKind::Return(value) => {
                self.return_slot = Some(self.const_eval_rvalue(value)?);
                Err(ConstEvalErrorKind::Return.into())
            }
            ExprKind::Call(callee, args) => {
                let callee = self.const_eval_rvalue(callee)?;
                let (arg_spec, expr, local_defs) = match callee {
                    Value::FunctionPointer(fun) => {
                        let func = fun
                            .get_function()
                            .map_err(|_| ConstEvalErrorKind::Unsupported)?;

                        let (body, local_defs) = func
                            .body
                            .get()
                            .and_then(|b| b.raw_body.map(|rb| (rb, b.local_defs)))
                            .ok_or_else(|| {
                                ConstEvalErrorKind::UnsupportedFunction(
                                    func.name.unwrap_or("<unnamed>").to_string(),
                                )
                            })?;

                        (func.args, body, local_defs)
                    }
                    _ => return Err(ConstEvalErrorKind::Unsupported.into()),
                };

                let mut remapped_variables = HashMap::default();
                for local_def in local_defs {
                    let new_id = self.ir.make_id();
                    remapped_variables.insert(local_def.id, new_id);

                    self.ctx.declare(new_id, local_def.typ);
                }

                for (arg, arg_spec) in args.iter().zip(arg_spec) {
                    let arg = self.const_eval_rvalue(arg)?;
                    let new_id = self.ir.make_id();
                    remapped_variables.insert(arg_spec.id, new_id);

                    self.ctx.define(new_id, arg);
                }

                let mut child = self.make_child(remapped_variables)?;

                let ret = match child.const_eval_rvalue(expr) {
                    Ok(value) => Ok(value),
                    Err(ConstEvalError {
                        kind: ConstEvalErrorKind::Return,
                        ..
                    }) => {
                        let value = child.return_slot.take().unwrap();
                        Ok(value)
                    }
                    Err(e) => Err(e),
                };
                ret
            }

            ExprKind::Static(_) => Err(ConstEvalErrorKind::Unsupported.into()),
            ExprKind::Unreachable => Err(ConstEvalErrorKind::ToReachTheUnreachableStar.into()),
        }
    }

    // Handle pointer arithmetic
    fn plus_minus(&mut self, lhs: Value<'ir>, op: BinOp, rhs: Value<'ir>) -> Result<Value<'ir>> {
        macro_rules! offset {
            () => {
                match rhs {
                    // if you do offsets > isize::MAX in const-eval, you are on your own
                    Value::USize(i) => i as isize,
                    Value::ISize(i) => i,
                    _ => return Err(ConstEvalErrorKind::Unsupported.into()),
                }
            };
        }

        match (lhs, rhs) {
            (
                Value::Pointer(LValue::Index(a, a_offset)),
                Value::Pointer(LValue::Index(b, b_offset)),
            ) if op == BinOp::Minus => {
                if b != a {
                    return Err(ConstEvalErrorKind::IndexOutOfBounds.into());
                }

                let diff = (a_offset as isize) - (b_offset as isize);
                return Ok(Value::ISize(diff));
            }
            (Value::Str(buf, offset), _) => {
                let new_offset = match op {
                    BinOp::Plus => (offset as isize) + offset!(),
                    BinOp::Minus => (offset as isize) + offset!(),
                    _ => return Err(ConstEvalErrorKind::CompilerBug.into()),
                };
                if new_offset < 0 || new_offset > (buf.len() as isize) {
                    return Err(ConstEvalErrorKind::IndexOutOfBounds.into());
                }
                return Ok(Value::Str(buf, new_offset as usize));
            }
            (Value::Pointer(LValue::Index(inner, offset)), _) => {
                let arr = match self.materialize_lvalue(*inner)? {
                    Value::Array(arr) => arr,
                    _ => return Err(ConstEvalErrorKind::Unsupported.into()),
                };

                let new_offset = match op {
                    BinOp::Plus => (offset as isize) + offset!(),
                    BinOp::Minus => (offset as isize) + offset!(),
                    _ => return Err(ConstEvalErrorKind::CompilerBug.into()),
                };
                if new_offset < 0 || new_offset > (arr.len() as isize) {
                    return Err(ConstEvalErrorKind::IndexOutOfBounds.into());
                }
                return Ok(Value::Pointer(LValue::Index(inner, new_offset as usize)));
            }

            _ => {}
        }

        match op {
            BinOp::Plus => lhs + rhs,
            BinOp::Minus => lhs - rhs,
            _ => unreachable!(),
        }
    }

    fn bin_op(&mut self, lhs: Value<'ir>, op: BinOp, rhs: Value<'ir>) -> Result<Value<'ir>> {
        match op {
            BinOp::BitAnd => lhs & rhs,
            BinOp::BitOr => lhs | rhs,
            BinOp::BitXor => lhs ^ rhs,
            BinOp::Or => lhs | rhs,
            BinOp::And => lhs & rhs,
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
            BinOp::Mul => lhs * rhs,
            BinOp::Div => lhs / rhs,
            BinOp::Mod => lhs % rhs,
            BinOp::Plus | BinOp::Minus => self.plus_minus(lhs, op, rhs),
        }
    }
}

fn check_lvalue_leak(value: &Value<'_>) -> Result<()> {
    match value {
        Value::Pointer(_) | Value::LValue(_) => Err(ConstEvalErrorKind::LValueLeak.into()),
        Value::Tuple(values) => values.iter().try_for_each(check_lvalue_leak),
        Value::Struct(fields) => fields
            .iter()
            .map(|(_, v)| v)
            .try_for_each(check_lvalue_leak),
        Value::Array(values) => values.iter().try_for_each(check_lvalue_leak),
        _ => Ok(()),
    }
}

fn make_uninitialized<'ir>(ir: &'ir IrCtx<'ir>, typ: TyP<'ir>) -> Value<'ir> {
    match typ {
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
            IRItem::StructLike(s) => {
                let fields = s.fields.iter().map(|f| {
                    let value = make_uninitialized(ir, f.ty);
                    (f.id, value)
                });

                Value::Struct(ir.arena.alloc_slice_fill_iter(fields))
            }
            _ => Value::Uninitialized,
        },
        _ => Value::Uninitialized,
    }
}
