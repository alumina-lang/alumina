use crate::common::{CodeErrorBuilder, CodeErrorKind};
use crate::ir::builder::TypeBuilder;
use crate::ir::const_eval::Value;
use crate::ir::{const_eval, Lit};
use crate::{ast::BuiltinType, common::AluminaError};

use crate::ir::{builder::ExpressionBuilder, ExprP, IrCtx, Ty, TyP};

use std::collections::HashMap;

use once_cell::sync::OnceCell;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntrinsicKind {
    SizeOf,
    AlignOf,
    TypeId,
    Trap,
    CompileFail,
    Unreachable,
    AlignedAlloca,
}

pub fn intrinsic_kind(name: &str) -> Option<IntrinsicKind> {
    static MAP: OnceCell<HashMap<&'static str, IntrinsicKind>> = OnceCell::new();
    MAP.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("size_of", IntrinsicKind::SizeOf);
        map.insert("align_of", IntrinsicKind::AlignOf);
        map.insert("type_id", IntrinsicKind::TypeId);
        map.insert("trap", IntrinsicKind::Trap);
        map.insert("compile_fail", IntrinsicKind::CompileFail);
        map.insert("unreachable", IntrinsicKind::Unreachable);
        map.insert("aligned_alloca", IntrinsicKind::AlignedAlloca);
        map
    })
    .get(name)
    .copied()
}

macro_rules! typecheck {
    ($expected:expr, $actual:expr) => {
        if !$expected.assignable_from($actual) {
            return Err(crate::common::CodeErrorKind::TypeMismatch(
                format!("{:?}", $expected),
                format!("{:?}", $actual),
            ))
            .with_no_span();
        }
    };
}

#[derive(Debug, Clone)]
pub enum CodegenIntrinsicKind<'ir> {
    SizeOfLike(&'ir str, TyP<'ir>),
    FunctionLike(&'ir str),
}

pub struct CompilerIntrinsics<'ir> {
    ir: &'ir IrCtx<'ir>,
    expressions: ExpressionBuilder<'ir>,
    types: TypeBuilder<'ir>,
}

impl<'ir> CompilerIntrinsics<'ir> {
    pub fn new(ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            expressions: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
        }
    }

    fn size_of(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        if ty.is_zero_sized() {
            return Ok(self.expressions.const_value(Value::USize(0)));
        }

        Ok(self.expressions.codegen_intrinsic(
            CodegenIntrinsicKind::SizeOfLike("sizeof", ty),
            self.types.builtin(BuiltinType::USize),
        ))
    }

    fn align_of(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        if ty.is_zero_sized() {
            return Ok(self.expressions.const_value(Value::USize(1)));
        }

        Ok(self.expressions.codegen_intrinsic(
            CodegenIntrinsicKind::SizeOfLike("_Alignof", ty),
            self.types.builtin(BuiltinType::USize),
        ))
    }

    fn type_id(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        // just in case someone made a copy
        let interned = self.ir.intern_type(*ty);

        // This will obviously not be stable between compilations, but for
        // now it's fine since we always monomorphize everything. Needs to be
        // retought if incremental compilation is ever implemented.
        let id = interned as *const Ty<'ir> as usize;

        Ok(self.expressions.const_value(Value::USize(id)))
    }

    fn compile_fail(&self, reason: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let value = const_eval::const_eval(reason)
            .map_err(|_| CodeErrorKind::CannotConstEvaluate)
            .with_no_span()?;

        Err(CodeErrorKind::ExplicitCompileFail(value.to_string())).with_no_span()
    }

    fn unreachable(&self) -> Result<ExprP<'ir>, AluminaError> {
        Ok(self.expressions.unreachable())
    }

    fn trap(&self) -> Result<ExprP<'ir>, AluminaError> {
        let ret_type = self.types.builtin(BuiltinType::Never);
        let fn_type = self.types.function([], ret_type);

        Ok(self.expressions.call(
            self.expressions.codegen_intrinsic(
                CodegenIntrinsicKind::FunctionLike("__builtin_trap"),
                fn_type,
            ),
            [],
            ret_type,
        ))
    }

    fn aligned_alloca(
        &self,
        size: ExprP<'ir>,
        align: ExprP<'ir>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        typecheck!(Ty::Builtin(BuiltinType::USize), size.ty);
        typecheck!(Ty::Builtin(BuiltinType::USize), align.ty);

        let ret_type = self
            .types
            .pointer(self.types.builtin(BuiltinType::Void), false);
        let fn_type = self.types.function(
            vec![
                self.types.builtin(BuiltinType::USize),
                self.types.builtin(BuiltinType::USize),
            ],
            ret_type,
        );

        Ok(self.expressions.call(
            self.expressions.codegen_intrinsic(
                CodegenIntrinsicKind::FunctionLike("__builtin_alloca_with_align"),
                fn_type,
            ),
            [size, align],
            ret_type,
        ))
    }

    pub fn invoke(
        &self,
        kind: IntrinsicKind,
        generic: &[TyP<'ir>],
        args: &[ExprP<'ir>],
    ) -> Result<ExprP<'ir>, AluminaError> {
        // Fine to panic when indexing here, if someone tried to change the signature
        // of the intrinsic in standard library, they deserve to have the compiler crash.
        match kind {
            IntrinsicKind::SizeOf => self.size_of(generic[0]),
            IntrinsicKind::AlignOf => self.align_of(generic[0]),
            IntrinsicKind::TypeId => self.type_id(generic[0]),
            IntrinsicKind::Trap => self.trap(),
            IntrinsicKind::CompileFail => self.compile_fail(args[0]),
            IntrinsicKind::Unreachable => self.unreachable(),
            IntrinsicKind::AlignedAlloca => self.aligned_alloca(args[0], args[1]),
        }
    }
}
