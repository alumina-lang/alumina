use crate::ast::{BinOp, BuiltinType};
use crate::common::CodeDiagnostic;
use crate::utils::regex;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItemKind {
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
    ProtoArrayOf,
    ProtoPointerOf,
    ProtoRangeOf,
    ProtoMeta,
    ProtoSameLayoutAs,
    ProtoSameBaseAs,
    ProtoAny,
    ProtoNone,

    ImplBuiltin(BuiltinType),
    ImplTuple(usize),
    ImplArray,

    TypeopTupleHeadOf,
    TypeopTupleTailOf,
    TypeopReturnTypeOf,
    TypeopArgumentsOf,
    TypeopPointerWithMutOf,
    TypeopArrayWithLengthOf,
    TypeopGenericArgsOf,
    TypeopEnumTypeOf,

    EntrypointGlue,
    TestCaseMeta,
    TestCaseMetaNew,

    Dyn,
    DynSelf,
    DynNew,
    DynConstCoerce,
    DynConstCast,
    DynData,
    DynVtableIndex,

    Operator(BinOp),

    FormatArg,
    EnumVariantNew,
}

impl LangItemKind {
    pub fn is_builtin_protocol(&self) -> bool {
        matches!(
            self,
            LangItemKind::ProtoPrimitive
                | LangItemKind::ProtoNumeric
                | LangItemKind::ProtoInteger
                | LangItemKind::ProtoFloatingPoint
                | LangItemKind::ProtoSigned
                | LangItemKind::ProtoUnsigned
                | LangItemKind::ProtoZeroSized
                | LangItemKind::ProtoPointer
                | LangItemKind::ProtoArray
                | LangItemKind::ProtoTuple
                | LangItemKind::ProtoRange
                | LangItemKind::ProtoEnum
                | LangItemKind::ProtoStruct
                | LangItemKind::ProtoUnion
                | LangItemKind::ProtoCallable
                | LangItemKind::ProtoNamedFunction
                | LangItemKind::ProtoFunctionPointer
                | LangItemKind::ProtoArrayOf
                | LangItemKind::ProtoPointerOf
                | LangItemKind::ProtoMeta
                | LangItemKind::ProtoRangeOf
        )
    }

    pub fn is_typeop(&self) -> bool {
        matches!(
            self,
            LangItemKind::TypeopTupleHeadOf
                | LangItemKind::TypeopTupleTailOf
                | LangItemKind::TypeopReturnTypeOf
                | LangItemKind::TypeopArgumentsOf
                | LangItemKind::TypeopPointerWithMutOf
                | LangItemKind::TypeopArrayWithLengthOf
                | LangItemKind::TypeopEnumTypeOf
                | LangItemKind::TypeopGenericArgsOf
        )
    }

    pub fn is_builtin_impl(&self) -> bool {
        matches!(
            self,
            LangItemKind::ImplBuiltin(_) | LangItemKind::ImplTuple(_) | LangItemKind::ImplArray
        )
    }
}

impl TryFrom<&str> for LangItemKind {
    type Error = CodeDiagnostic;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "slice" => Ok(LangItemKind::Slice),
            "slice_new" => Ok(LangItemKind::SliceNew),
            "slice_const_coerce" => Ok(LangItemKind::SliceConstCoerce),
            "slice_const_cast" => Ok(LangItemKind::SliceConstCast),
            "slice_index" => Ok(LangItemKind::SliceIndex),
            "slice_range_index" => Ok(LangItemKind::SliceRangeIndex),
            "slice_slicify" => Ok(LangItemKind::SliceSlicify),

            "range_full" => Ok(LangItemKind::RangeFull),
            "range_from" => Ok(LangItemKind::RangeFrom),
            "range_to" => Ok(LangItemKind::RangeTo),
            "range_to_inclusive" => Ok(LangItemKind::RangeToInclusive),
            "range" => Ok(LangItemKind::Range),
            "range_inclusive" => Ok(LangItemKind::RangeInclusive),

            "range_full_new" => Ok(LangItemKind::RangeFullNew),
            "range_from_new" => Ok(LangItemKind::RangeFromNew),
            "range_to_new" => Ok(LangItemKind::RangeToNew),
            "range_new" => Ok(LangItemKind::RangeNew),
            "range_to_inclusive_new" => Ok(LangItemKind::RangeToInclusiveNew),
            "range_inclusive_new" => Ok(LangItemKind::RangeInclusiveNew),

            "proto_primitive" => Ok(LangItemKind::ProtoPrimitive),
            "proto_numeric" => Ok(LangItemKind::ProtoNumeric),
            "proto_integer" => Ok(LangItemKind::ProtoInteger),
            "proto_floating_point" => Ok(LangItemKind::ProtoFloatingPoint),
            "proto_signed" => Ok(LangItemKind::ProtoSigned),
            "proto_unsigned" => Ok(LangItemKind::ProtoUnsigned),
            "proto_pointer" => Ok(LangItemKind::ProtoPointer),
            "proto_zero_sized" => Ok(LangItemKind::ProtoZeroSized),
            "proto_array" => Ok(LangItemKind::ProtoArray),
            "proto_struct" => Ok(LangItemKind::ProtoStruct),
            "proto_enum" => Ok(LangItemKind::ProtoEnum),
            "proto_union" => Ok(LangItemKind::ProtoUnion),
            "proto_tuple" => Ok(LangItemKind::ProtoTuple),
            "proto_range" => Ok(LangItemKind::ProtoRange),
            "proto_named_function" => Ok(LangItemKind::ProtoNamedFunction),
            "proto_function_pointer" => Ok(LangItemKind::ProtoFunctionPointer),
            "proto_callable" => Ok(LangItemKind::ProtoCallable),
            "proto_array_of" => Ok(LangItemKind::ProtoArrayOf),
            "proto_pointer_of" => Ok(LangItemKind::ProtoPointerOf),
            "proto_range_of" => Ok(LangItemKind::ProtoRangeOf),
            "proto_meta" => Ok(LangItemKind::ProtoMeta),
            "proto_same_layout_as" => Ok(LangItemKind::ProtoSameLayoutAs),
            "proto_same_base_as" => Ok(LangItemKind::ProtoSameBaseAs),
            "proto_any" => Ok(LangItemKind::ProtoAny),
            "proto_none" => Ok(LangItemKind::ProtoNone),

            "builtin_never" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Never)),
            "builtin_void" => Ok(LangItemKind::ImplTuple(0)),
            "builtin_bool" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Bool)),
            "builtin_u8" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U8)),
            "builtin_u16" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U16)),
            "builtin_u32" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U32)),
            "builtin_u64" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U64)),
            "builtin_u128" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U128)),
            "builtin_usize" => Ok(LangItemKind::ImplBuiltin(BuiltinType::USize)),
            "builtin_i8" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I8)),
            "builtin_i16" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I16)),
            "builtin_i32" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I32)),
            "builtin_i64" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I64)),
            "builtin_i128" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I128)),
            "builtin_isize" => Ok(LangItemKind::ImplBuiltin(BuiltinType::ISize)),
            "builtin_f32" => Ok(LangItemKind::ImplBuiltin(BuiltinType::F32)),
            "builtin_f64" => Ok(LangItemKind::ImplBuiltin(BuiltinType::F64)),

            "builtin_array" => Ok(LangItemKind::ImplArray),

            "operator_eq" => Ok(LangItemKind::Operator(BinOp::Eq)),
            "operator_neq" => Ok(LangItemKind::Operator(BinOp::Neq)),
            "operator_lt" => Ok(LangItemKind::Operator(BinOp::Lt)),
            "operator_lte" => Ok(LangItemKind::Operator(BinOp::LEq)),
            "operator_gt" => Ok(LangItemKind::Operator(BinOp::Gt)),
            "operator_gte" => Ok(LangItemKind::Operator(BinOp::GEq)),

            "typeop_tuple_head_of" => Ok(LangItemKind::TypeopTupleHeadOf),
            "typeop_tuple_tail_of" => Ok(LangItemKind::TypeopTupleTailOf),
            "typeop_return_type_of" => Ok(LangItemKind::TypeopReturnTypeOf),
            "typeop_arguments_of" => Ok(LangItemKind::TypeopArgumentsOf),
            "typeop_pointer_with_mut_of" => Ok(LangItemKind::TypeopPointerWithMutOf),
            "typeop_array_with_length_of" => Ok(LangItemKind::TypeopArrayWithLengthOf),
            "typeop_generic_args_of" => Ok(LangItemKind::TypeopGenericArgsOf),
            "typeop_enum_type_of" => Ok(LangItemKind::TypeopEnumTypeOf),

            "entrypoint_glue" => Ok(LangItemKind::EntrypointGlue),
            "test_case_meta" => Ok(LangItemKind::TestCaseMeta),
            "test_case_meta_new" => Ok(LangItemKind::TestCaseMetaNew),

            "dyn" => Ok(LangItemKind::Dyn),
            "dyn_self" => Ok(LangItemKind::DynSelf),
            "dyn_new" => Ok(LangItemKind::DynNew),
            "dyn_const_coerce" => Ok(LangItemKind::DynConstCoerce),
            "dyn_const_cast" => Ok(LangItemKind::DynConstCast),
            "dyn_data" => Ok(LangItemKind::DynData),
            "dyn_vtable_index" => Ok(LangItemKind::DynVtableIndex),

            "format_arg" => Ok(LangItemKind::FormatArg),
            "enum_variant_new" => Ok(LangItemKind::EnumVariantNew),

            t => {
                if let Some(matches) = regex!(r"^builtin_tuple_(\d+)$").captures(t) {
                    let n = matches[1].parse::<usize>().unwrap();
                    Ok(LangItemKind::ImplTuple(n))
                } else {
                    Err(CodeDiagnostic::UnknownLangItem(Some(t.to_string())))
                }
            }
        }
    }
}
