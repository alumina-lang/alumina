use crate::ir::{ExprP, TyP};

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
    Zeroed,
    Asm,
    InConstContext,
    IsConstEvaluable,
    ConstEval,
    ConstPanic,
    ConstWarning,
    ConstNote,
    ConstAlloc,
    ConstFree,
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
        "zeroed" => IntrinsicKind::Zeroed,
        "in_const_context" => IntrinsicKind::InConstContext,
        "is_const_evaluable" => IntrinsicKind::IsConstEvaluable,
        "const_eval" => IntrinsicKind::ConstEval,
        "const_panic" => IntrinsicKind::ConstPanic,
        "const_warning" => IntrinsicKind::ConstWarning,
        "const_note" => IntrinsicKind::ConstNote,
        "const_alloc" => IntrinsicKind::ConstAlloc,
        "const_free" => IntrinsicKind::ConstFree,
        _ => return None,
    };

    Some(ret)
}

#[derive(Debug, Clone)]
pub enum IntrinsicValueKind<'ir> {
    SizeOfLike(&'ir str, TyP<'ir>),
    Dangling(TyP<'ir>),
    Asm(&'ir str),
    FunctionLike(&'ir str),
    ConstLike(&'ir str),
    ConstPanic(ExprP<'ir>),
    ConstWrite(ExprP<'ir>, bool),
    ConstAlloc(TyP<'ir>, ExprP<'ir>),
    ConstFree(ExprP<'ir>),
    Uninitialized,
    InConstContext,
}
