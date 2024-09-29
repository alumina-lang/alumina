use alumina_boot_macros::AstSerializable;

use crate::ast::{BinOp, BuiltinType};
use crate::common::CodeDiagnostic;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, AstSerializable)]
pub enum Lang {
    Slice,
    SliceNew,
    SliceIndex,
    SliceRangeIndex,
    SliceConstCoerce,
    SliceConstCast,
    SliceSlicify,

    RangeFull,
    RangeFrom,
    RangeTo,
    RangeToInclusive,
    Range,
    RangeInclusive,
    RangeFullNew,
    RangeFromNew,
    RangeToNew,
    RangeToInclusiveNew,
    RangeNew,
    RangeInclusiveNew,

    ProtoPrimitive,
    ProtoNumeric,
    ProtoInteger,
    ProtoFloatingPoint,
    ProtoSigned,
    ProtoUnsigned,
    ProtoZeroSized,
    ProtoPointer,
    ProtoArray,
    ProtoTuple,
    ProtoRange,
    ProtoStruct,
    ProtoEnum,
    ProtoUnion,
    ProtoCallable,
    ProtoNamedFunction,
    ProtoFunctionPointer,
    ProtoClosure,
    ProtoConst,
    ProtoStatic,
    ProtoArrayOf,
    ProtoPointerOf,
    ProtoRangeOf,
    ProtoMeta,
    ProtoSameLayoutAs,
    ProtoSameBaseAs,
    ProtoAny,
    ProtoNone,

    ImplBuiltin(BuiltinType),
    ImplTuple,
    ImplArray,
    ImplCallable,

    TypeopReturnTypeOf,
    TypeopArgumentsOf,
    TypeopPointerWithMutOf,
    TypeopArrayWithLengthOf,
    TypeopGenericArgsOf,
    TypeopReplaceGenericArgsOf,
    TypeopFunctionPointerOf,
    TypeopUnderlyingTypeOf,
    TypeopUnderlyingFunctionOf,

    EntrypointGlue,

    Dyn,
    DynSelf,
    DynNew,
    DynConstCoerce,
    DynConstCast,
    DynData,
    DynVtableIndex,

    Coroutine,
    CoroutineNew,
    CoroutineYield,

    Operator(BinOp),

    FormatArg,
    EnumVariantNew,
    FieldDescriptorNew,
    FieldDescriptorNewUnnamed,
    TypeDescriptorNew,

    StaticForIter,
    StaticForNext,
}

impl Lang {
    pub fn is_builtin_protocol(&self) -> bool {
        matches!(
            self,
            Lang::ProtoPrimitive
                | Lang::ProtoNumeric
                | Lang::ProtoInteger
                | Lang::ProtoFloatingPoint
                | Lang::ProtoSigned
                | Lang::ProtoUnsigned
                | Lang::ProtoZeroSized
                | Lang::ProtoPointer
                | Lang::ProtoArray
                | Lang::ProtoTuple
                | Lang::ProtoRange
                | Lang::ProtoEnum
                | Lang::ProtoStruct
                | Lang::ProtoUnion
                | Lang::ProtoCallable
                | Lang::ProtoNamedFunction
                | Lang::ProtoFunctionPointer
                | Lang::ProtoClosure
                | Lang::ProtoConst
                | Lang::ProtoStatic
                | Lang::ProtoArrayOf
                | Lang::ProtoPointerOf
                | Lang::ProtoMeta
                | Lang::ProtoRangeOf
        )
    }

    pub fn is_typeop(&self) -> bool {
        matches!(
            self,
            Lang::TypeopReturnTypeOf
                | Lang::TypeopArgumentsOf
                | Lang::TypeopPointerWithMutOf
                | Lang::TypeopArrayWithLengthOf
                | Lang::TypeopGenericArgsOf
                | Lang::TypeopReplaceGenericArgsOf
                | Lang::TypeopFunctionPointerOf
                | Lang::TypeopUnderlyingTypeOf
        )
    }

    pub fn is_builtin_impl(&self) -> bool {
        matches!(
            self,
            Lang::ImplBuiltin(_) | Lang::ImplTuple | Lang::ImplArray
        )
    }
}

impl TryFrom<&str> for Lang {
    type Error = CodeDiagnostic;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "slice" => Ok(Lang::Slice),
            "slice_new" => Ok(Lang::SliceNew),
            "slice_const_coerce" => Ok(Lang::SliceConstCoerce),
            "slice_const_cast" => Ok(Lang::SliceConstCast),
            "slice_index" => Ok(Lang::SliceIndex),
            "slice_range_index" => Ok(Lang::SliceRangeIndex),
            "slice_slicify" => Ok(Lang::SliceSlicify),

            "range_full" => Ok(Lang::RangeFull),
            "range_from" => Ok(Lang::RangeFrom),
            "range_to" => Ok(Lang::RangeTo),
            "range_to_inclusive" => Ok(Lang::RangeToInclusive),
            "range" => Ok(Lang::Range),
            "range_inclusive" => Ok(Lang::RangeInclusive),

            "range_full_new" => Ok(Lang::RangeFullNew),
            "range_from_new" => Ok(Lang::RangeFromNew),
            "range_to_new" => Ok(Lang::RangeToNew),
            "range_new" => Ok(Lang::RangeNew),
            "range_to_inclusive_new" => Ok(Lang::RangeToInclusiveNew),
            "range_inclusive_new" => Ok(Lang::RangeInclusiveNew),

            "proto_primitive" => Ok(Lang::ProtoPrimitive),
            "proto_numeric" => Ok(Lang::ProtoNumeric),
            "proto_integer" => Ok(Lang::ProtoInteger),
            "proto_floating_point" => Ok(Lang::ProtoFloatingPoint),
            "proto_signed" => Ok(Lang::ProtoSigned),
            "proto_unsigned" => Ok(Lang::ProtoUnsigned),
            "proto_pointer" => Ok(Lang::ProtoPointer),
            "proto_zero_sized" => Ok(Lang::ProtoZeroSized),
            "proto_array" => Ok(Lang::ProtoArray),
            "proto_struct" => Ok(Lang::ProtoStruct),
            "proto_enum" => Ok(Lang::ProtoEnum),
            "proto_union" => Ok(Lang::ProtoUnion),
            "proto_tuple" => Ok(Lang::ProtoTuple),
            "proto_range" => Ok(Lang::ProtoRange),
            "proto_named_function" => Ok(Lang::ProtoNamedFunction),
            "proto_function_pointer" => Ok(Lang::ProtoFunctionPointer),
            "proto_closure" => Ok(Lang::ProtoClosure),
            "proto_const" => Ok(Lang::ProtoConst),
            "proto_static" => Ok(Lang::ProtoStatic),
            "proto_callable" => Ok(Lang::ProtoCallable),
            "proto_array_of" => Ok(Lang::ProtoArrayOf),
            "proto_pointer_of" => Ok(Lang::ProtoPointerOf),
            "proto_range_of" => Ok(Lang::ProtoRangeOf),
            "proto_meta" => Ok(Lang::ProtoMeta),
            "proto_same_layout_as" => Ok(Lang::ProtoSameLayoutAs),
            "proto_same_base_as" => Ok(Lang::ProtoSameBaseAs),
            "proto_any" => Ok(Lang::ProtoAny),
            "proto_none" => Ok(Lang::ProtoNone),

            "builtin_never" => Ok(Lang::ImplBuiltin(BuiltinType::Never)),
            "builtin_bool" => Ok(Lang::ImplBuiltin(BuiltinType::Bool)),
            "builtin_u8" => Ok(Lang::ImplBuiltin(BuiltinType::U8)),
            "builtin_u16" => Ok(Lang::ImplBuiltin(BuiltinType::U16)),
            "builtin_u32" => Ok(Lang::ImplBuiltin(BuiltinType::U32)),
            "builtin_u64" => Ok(Lang::ImplBuiltin(BuiltinType::U64)),
            "builtin_u128" => Ok(Lang::ImplBuiltin(BuiltinType::U128)),
            "builtin_usize" => Ok(Lang::ImplBuiltin(BuiltinType::USize)),
            "builtin_i8" => Ok(Lang::ImplBuiltin(BuiltinType::I8)),
            "builtin_i16" => Ok(Lang::ImplBuiltin(BuiltinType::I16)),
            "builtin_i32" => Ok(Lang::ImplBuiltin(BuiltinType::I32)),
            "builtin_i64" => Ok(Lang::ImplBuiltin(BuiltinType::I64)),
            "builtin_i128" => Ok(Lang::ImplBuiltin(BuiltinType::I128)),
            "builtin_isize" => Ok(Lang::ImplBuiltin(BuiltinType::ISize)),
            "builtin_f32" => Ok(Lang::ImplBuiltin(BuiltinType::F32)),
            "builtin_f64" => Ok(Lang::ImplBuiltin(BuiltinType::F64)),

            "builtin_array" => Ok(Lang::ImplArray),
            "builtin_tuple" => Ok(Lang::ImplTuple),
            "builtin_callable" => Ok(Lang::ImplCallable),

            "operator_eq" => Ok(Lang::Operator(BinOp::Eq)),
            "operator_neq" => Ok(Lang::Operator(BinOp::Neq)),
            "operator_lt" => Ok(Lang::Operator(BinOp::Lt)),
            "operator_lte" => Ok(Lang::Operator(BinOp::LEq)),
            "operator_gt" => Ok(Lang::Operator(BinOp::Gt)),
            "operator_gte" => Ok(Lang::Operator(BinOp::GEq)),

            "typeop_return_type_of" => Ok(Lang::TypeopReturnTypeOf),
            "typeop_arguments_of" => Ok(Lang::TypeopArgumentsOf),
            "typeop_pointer_with_mut_of" => Ok(Lang::TypeopPointerWithMutOf),
            "typeop_array_with_length_of" => Ok(Lang::TypeopArrayWithLengthOf),
            "typeop_generic_args_of" => Ok(Lang::TypeopGenericArgsOf),
            "typeop_replace_generic_args_of" => Ok(Lang::TypeopReplaceGenericArgsOf),
            "typeop_function_pointer_of" => Ok(Lang::TypeopFunctionPointerOf),
            "typeop_underlying_type_of" => Ok(Lang::TypeopUnderlyingTypeOf),
            "typeop_underlying_function_of" => Ok(Lang::TypeopUnderlyingFunctionOf),

            "entrypoint_glue" => Ok(Lang::EntrypointGlue),

            "dyn" => Ok(Lang::Dyn),
            "dyn_self" => Ok(Lang::DynSelf),
            "dyn_new" => Ok(Lang::DynNew),
            "dyn_const_coerce" => Ok(Lang::DynConstCoerce),
            "dyn_const_cast" => Ok(Lang::DynConstCast),
            "dyn_data" => Ok(Lang::DynData),
            "dyn_vtable_index" => Ok(Lang::DynVtableIndex),

            "coroutine" => Ok(Lang::Coroutine),
            "coroutine_new" => Ok(Lang::CoroutineNew),
            "coroutine_yield" => Ok(Lang::CoroutineYield),

            "format_arg" => Ok(Lang::FormatArg),
            "enum_variant_new" => Ok(Lang::EnumVariantNew),
            "field_descriptor_new" => Ok(Lang::FieldDescriptorNew),
            "field_descriptor_new_unnamed" => Ok(Lang::FieldDescriptorNewUnnamed),
            "type_descriptor_new" => Ok(Lang::TypeDescriptorNew),

            "static_for_iter" => Ok(Lang::StaticForIter),
            "static_for_next" => Ok(Lang::StaticForNext),

            t => Err(CodeDiagnostic::UnknownLangItem(t.to_string())),
        }
    }
}
