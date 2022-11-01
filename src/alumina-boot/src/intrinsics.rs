use crate::ast::{BuiltinType, Span};
use crate::common::{AluminaError, CodeError, CodeErrorBuilder, CodeErrorKind};
use crate::global_ctx::GlobalCtx;
use crate::ir::builder::{ExpressionBuilder, TypeBuilder};
use crate::ir::const_eval::{
    Value, {self},
};
use crate::ir::layout::Layouter;
use crate::ir::{ExprP, IrCtx, Ty, TyP, ValueType};

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
    CodegenTypeFunc,
    MakeVtable,
    EnumVariants,
    Uninitialized,
    Dangling,
    Asm,
}

pub fn intrinsic_kind(name: &str) -> Option<IntrinsicKind> {
    let ret = match name {
        "size_of" => IntrinsicKind::SizeOf,
        "align_of" => IntrinsicKind::AlignOf,
        "array_length_of" => IntrinsicKind::ArrayLengthOf,
        "type_id" => IntrinsicKind::TypeId,
        "type_name" => IntrinsicKind::TypeName,
        "trap" => IntrinsicKind::Trap,
        "compile_fail" => IntrinsicKind::CompileFail,
        "compile_warn" => IntrinsicKind::CompileWarn,
        "compile_note" => IntrinsicKind::CompileNote,
        "unreachable" => IntrinsicKind::Unreachable,
        "test_cases" => IntrinsicKind::TestCases,
        "codegen_func" => IntrinsicKind::CodegenFunc,
        "codegen_const" => IntrinsicKind::CodegenConst,
        "codegen_type_func" => IntrinsicKind::CodegenTypeFunc,
        "vtable" => IntrinsicKind::MakeVtable,
        "enum_variants" => IntrinsicKind::EnumVariants,
        "asm" => IntrinsicKind::Asm,
        "uninitialized" => IntrinsicKind::Uninitialized,
        "dangling" => IntrinsicKind::Dangling,
        _ => return None,
    };

    Some(ret)
}

#[derive(Debug, Clone)]
pub enum CodegenIntrinsicKind<'ir> {
    SizeOfLike(&'ir str, TyP<'ir>),
    Dangling(TyP<'ir>),
    Asm(&'ir str),
    FunctionLike(&'ir str),
    ConstLike(&'ir str),
    Uninitialized,
}

pub struct CompilerIntrinsics<'ir> {
    ir: &'ir IrCtx<'ir>,
    global_ctx: GlobalCtx,
    expressions: ExpressionBuilder<'ir>,
    layouter: Layouter<'ir>,
    types: TypeBuilder<'ir>,
}

/// This is a bit of a hack, ideally a new lang method would be used to extract this,
/// but I don't particularly want to plum lang methods into this module right now.
/// String slices are the only thing that can produce Value::Str(...), so this is unlikely
/// to lead to surprises.
fn extract_constant_string_from_slice<'ir>(value: &Value<'ir>) -> Option<&'ir [u8]> {
    match value {
        Value::Struct(fields) => {
            for (_id, value) in fields.iter() {
                if let Value::Str(r) = value {
                    return Some(r);
                }
            }
            None
        }
        _ => None,
    }
}

impl<'ir> CompilerIntrinsics<'ir> {
    pub fn new(global_ctx: GlobalCtx, ir: &'ir IrCtx<'ir>) -> Self {
        Self {
            ir,
            expressions: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            layouter: Layouter::new(global_ctx.clone()),
            global_ctx,
        }
    }

    fn get_const_string(&self, expr: ExprP<'ir>) -> Result<&'ir str, AluminaError> {
        match const_eval::ConstEvaluator::new(self.ir).const_eval(expr) {
            Ok(value) => {
                if let Some(r) = extract_constant_string_from_slice(&value) {
                    Ok(std::str::from_utf8(r).unwrap())
                } else {
                    Err(CodeErrorKind::TypeMismatch(
                        "constant string".to_string(),
                        format!("{:?}", expr.ty),
                    ))
                }
            }
            .with_no_span(),
            Err(e) => Err(CodeErrorKind::CannotConstEvaluate(e)).with_no_span(),
        }
    }

    fn align_of(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let align = self.layouter.layout_of(ty)?.align;

        Ok(self
            .expressions
            .literal(Value::USize(align), self.types.builtin(BuiltinType::USize)))
    }

    fn size_of(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let size = self.layouter.layout_of(ty)?.size;

        Ok(self
            .expressions
            .literal(Value::USize(size), self.types.builtin(BuiltinType::USize)))
    }

    fn type_id(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        // just in case someone made a copy
        let interned = self.ir.intern_type(*ty);

        // This will obviously not be stable between compilations, but for
        // now it's fine since we always monomorphize everything. Needs to be
        // retought if incremental compilation is ever implemented.
        let id = interned as *const Ty<'ir> as usize;

        Ok(self
            .expressions
            .literal(Value::USize(id), self.types.builtin(BuiltinType::USize)))
    }

    fn array_length_of(&self, ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        if let Ty::Array(_, len) = ty {
            return Ok(self
                .expressions
                .literal(Value::USize(*len), self.types.builtin(BuiltinType::USize)));
        }

        Err(CodeErrorKind::TypeMismatch(
            "array".to_string(),
            format!("{:?}", ty),
        ))
        .with_no_span()
    }

    fn compile_fail(&self, reason: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let reason = self.get_const_string(reason)?;

        Err(CodeErrorKind::UserDefined(reason.to_string())).with_no_span()
    }

    fn compile_warn(
        &self,
        reason: ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let reason = self.get_const_string(reason)?;

        self.global_ctx.diag().add_warning(CodeError::from_kind(
            CodeErrorKind::UserDefined(reason.to_string()),
            span,
        ));

        Ok(self.expressions.void(self.types.void(), ValueType::RValue))
    }

    fn compile_note(
        &self,
        reason: ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let reason = self.get_const_string(reason)?;

        self.global_ctx.diag().add_note(CodeError::from_kind(
            CodeErrorKind::UserDefined(reason.to_string()),
            span,
        ));

        Ok(self.expressions.void(self.types.void(), ValueType::RValue))
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
        let name = self.get_const_string(name)?;

        let arg_types = args.iter().map(|arg| arg.ty).collect::<Vec<_>>();
        let fn_type = self.types.function(arg_types, ret_ty);

        Ok(self.expressions.call(
            self.expressions
                .codegen_intrinsic(CodegenIntrinsicKind::FunctionLike(name), fn_type),
            args.iter().copied(),
            ret_ty,
        ))
    }

    fn codegen_type_func(
        &self,
        name: ExprP<'ir>,
        ty: TyP<'ir>,
        ret_ty: TyP<'ir>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let name = self.get_const_string(name)?;

        Ok(self
            .expressions
            .codegen_intrinsic(CodegenIntrinsicKind::SizeOfLike(name, ty), ret_ty))
    }

    fn asm(&self, assembly: ExprP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        let assembly = self.get_const_string(assembly)?;

        Ok(self
            .expressions
            .codegen_intrinsic(CodegenIntrinsicKind::Asm(assembly), self.types.void()))
    }

    fn codegen_const(
        &self,
        name: ExprP<'ir>,
        ret_ty: TyP<'ir>,
    ) -> Result<ExprP<'ir>, AluminaError> {
        let name = self.get_const_string(name)?;

        Ok(self
            .expressions
            .codegen_intrinsic(CodegenIntrinsicKind::ConstLike(name), ret_ty))
    }

    fn uninitialized(&self, ret_ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        Ok(self
            .expressions
            .codegen_intrinsic(CodegenIntrinsicKind::Uninitialized, ret_ty))
    }

    fn dangling(&self, ret_ty: TyP<'ir>) -> Result<ExprP<'ir>, AluminaError> {
        if let Ty::Pointer(inner, _) = ret_ty {
            Ok(self
                .expressions
                .codegen_intrinsic(CodegenIntrinsicKind::Dangling(inner), ret_ty))
        } else {
            Err(CodeErrorKind::TypeMismatch(
                "pointer".to_string(),
                format!("{:?}", ret_ty),
            ))
            .with_no_span()
        }
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
            IntrinsicKind::CodegenTypeFunc => {
                self.codegen_type_func(args[0], generic[0], generic[1])
            }
            IntrinsicKind::Uninitialized => self.uninitialized(generic[0]),
            IntrinsicKind::Dangling => self.dangling(generic[0]),
            _ => unreachable!(),
        }
    }
}
