use crate::ast::Span;
use crate::common::{CodeError, CodeErrorBuilder, CodeErrorKind};
use crate::global_ctx::GlobalCtx;
use crate::ir::builder::TypeBuilder;
use crate::ir::const_eval::Value;
use crate::ir::{const_eval, ValueType};
use crate::{ast::BuiltinType, common::AluminaError};

use crate::ir::{builder::ExpressionBuilder, ExprP, IrCtx, Ty, TyP};

use std::collections::HashMap;

use once_cell::sync::OnceCell;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntrinsicKind {
    SizeOf,
    AlignOf,
    ArrayLengthOf,
    TypeId,
    TypeName,
    Trap,
    CompileFail,
    CompileWarn,
    CompileNote,
    Unreachable,
    TestCases,
    CodegenFunc,
    CodegenConst,
    MakeVtable,
    EnumVariants,
    Uninitialized,
    Asm,
}

pub fn intrinsic_kind(name: &str) -> Option<IntrinsicKind> {
    static MAP: OnceCell<HashMap<&'static str, IntrinsicKind>> = OnceCell::new();
    MAP.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("size_of", IntrinsicKind::SizeOf);
        map.insert("align_of", IntrinsicKind::AlignOf);
        map.insert("array_length_of", IntrinsicKind::ArrayLengthOf);
        map.insert("type_id", IntrinsicKind::TypeId);
        map.insert("type_name", IntrinsicKind::TypeName);
        map.insert("trap", IntrinsicKind::Trap);
        map.insert("compile_fail", IntrinsicKind::CompileFail);
        map.insert("compile_warn", IntrinsicKind::CompileWarn);
        map.insert("compile_note", IntrinsicKind::CompileNote);
        map.insert("unreachable", IntrinsicKind::Unreachable);
        map.insert("test_cases", IntrinsicKind::TestCases);
        map.insert("codegen_func", IntrinsicKind::CodegenFunc);
        map.insert("codegen_const", IntrinsicKind::CodegenConst);
        map.insert("vtable", IntrinsicKind::MakeVtable);
        map.insert("enum_variants", IntrinsicKind::EnumVariants);
        map.insert("asm", IntrinsicKind::Asm);
        map.insert("uninitialized", IntrinsicKind::Uninitialized);
        map
    })
    .get(name)
    .copied()
}

#[derive(Debug, Clone)]
pub enum CodegenIntrinsicKind<'ir> {
    SizeOfLike(&'ir str, TyP<'ir>),
    Asm(&'ir str),
    FunctionLike(&'ir str),
    ConstLike(&'ir str),
    Uninitialized,
}

pub struct CompilerIntrinsics<'ir> {
    ir: &'ir IrCtx<'ir>,
    global_ctx: GlobalCtx,
    expressions: ExpressionBuilder<'ir>,
    types: TypeBuilder<'ir>,
}

fn get_const_string(expr: ExprP<'_>) -> Result<&str, AluminaError> {
    match const_eval::const_eval(expr) {
        Ok(Value::Str(s)) => Ok(std::str::from_utf8(s).unwrap()),
        Ok(v) => Err(CodeErrorKind::TypeMismatch(
            "string".to_string(),
            format!("{:?}", v.type_kind()),
        ))
        .with_no_span(),
        Err(e) => Err(CodeErrorKind::CannotConstEvaluate(e)).with_no_span(),
    }
}

impl<'ir> CompilerIntrinsics<'ir> {
    pub fn new(global_ctx: GlobalCtx, ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            expressions: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            global_ctx,
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
        if let Ty::Array(inner, _) = ty {
            // In Rust [i32; 0] has alignment of 4 instead of 1 as one would expect as it is a
            // ZST. I don't really know why, but I assume there's a good reason for it.
            return self.align_of(inner);
        }

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

    fn array_length_of(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        if let Ty::Array(_, len) = ty {
            return Ok(self.expressions.const_value(Value::USize(*len)));
        }

        Err(CodeErrorKind::TypeMismatch(
            "array".to_string(),
            format!("{:?}", ty),
        ))
        .with_no_span()
    }

    fn compile_fail(&self, reason: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let reason = get_const_string(reason)?;

        Err(CodeErrorKind::UserDefined(reason.to_string())).with_no_span()
    }

    fn compile_warn(
        &self,
        reason: ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let reason = get_const_string(reason)?;

        self.global_ctx.diag().add_warning(CodeError::from_kind(
            CodeErrorKind::UserDefined(reason.to_string()),
            span,
        ));

        Ok(self
            .expressions
            .void(self.types.builtin(BuiltinType::Void), ValueType::RValue))
    }

    fn compile_note(
        &self,
        reason: ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let reason = get_const_string(reason)?;

        self.global_ctx.diag().add_note(CodeError::from_kind(
            CodeErrorKind::UserDefined(reason.to_string()),
            span,
        ));

        Ok(self
            .expressions
            .void(self.types.builtin(BuiltinType::Void), ValueType::RValue))
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

    fn codegen_func(
        &self,
        name: ExprP<'ir>,
        args: &[ExprP<'ir>],
        ret_ty: TyP<'ir>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let name = get_const_string(name)?;

        let arg_types = args.iter().map(|arg| arg.ty).collect::<Vec<_>>();
        let fn_type = self.types.function(arg_types, ret_ty);

        Ok(self.expressions.call(
            self.expressions
                .codegen_intrinsic(CodegenIntrinsicKind::FunctionLike(name), fn_type),
            args.iter().copied(),
            ret_ty,
        ))
    }

    fn asm(&self, assembly: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let assembly = get_const_string(assembly)?;

        Ok(self.expressions.codegen_intrinsic(
            CodegenIntrinsicKind::Asm(assembly),
            self.types.builtin(BuiltinType::Void),
        ))
    }

    fn codegen_const(
        &self,
        name: ExprP<'ir>,
        ret_ty: TyP<'ir>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let name = get_const_string(name)?;

        Ok(self
            .expressions
            .codegen_intrinsic(CodegenIntrinsicKind::ConstLike(name), ret_ty))
    }

    fn uninitialized(&self, ret_ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        Ok(self
            .expressions
            .codegen_intrinsic(CodegenIntrinsicKind::Uninitialized, ret_ty))
    }

    pub fn invoke(
        &self,
        kind: IntrinsicKind,
        span: Option<Span>,
        generic: &[TyP<'ir>],
        args: &[ExprP<'ir>],
    ) -> Result<ExprP<'ir>, AluminaError> {
        // Fine to panic when indexing here, if someone tried to change the signature
        // of the intrinsic in standard library, they deserve to have the compiler crash.
        match kind {
            IntrinsicKind::SizeOf => self.size_of(generic[0]),
            IntrinsicKind::AlignOf => self.align_of(generic[0]),
            IntrinsicKind::TypeId => self.type_id(generic[0]),
            IntrinsicKind::ArrayLengthOf => self.array_length_of(generic[0]),
            IntrinsicKind::Trap => self.trap(),
            IntrinsicKind::CompileFail => self.compile_fail(args[0]),
            IntrinsicKind::CompileWarn => self.compile_warn(args[0], span),
            IntrinsicKind::CompileNote => self.compile_note(args[0], span),
            IntrinsicKind::Unreachable => self.unreachable(),
            IntrinsicKind::Asm => self.asm(args[0]),
            IntrinsicKind::CodegenFunc => self.codegen_func(args[0], &args[1..], generic[0]),
            IntrinsicKind::CodegenConst => self.codegen_const(args[0], generic[0]),
            IntrinsicKind::Uninitialized => self.uninitialized(generic[0]),
            _ => unreachable!(),
        }
    }
}
