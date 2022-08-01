use super::{BinOp, BuiltinType};
use crate::common::CodeErrorKind;
use crate::utils::regex;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItemKind {
    Slice,
    SliceNew,
    SliceIndex,
    SliceRangeIndex,
    SliceConstCoerce,
    SliceConstCast,

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
    ProtoCallable,
    ProtoNamedFunction,
    ProtoFunctionPointer,
    ProtoAny,
    ProtoArrayOf,
    ProtoPointerOf,
    ProtoRangeOf,

    // This one really shouldn't be a lang item, but I'm not smart
    // enough to figure out the type inference and iterator combinators
    // are really important for ergonomics.
    ProtoIterator,

    ImplBuiltin(BuiltinType),
    ImplTuple(usize),
    ImplArray,

    TypeopSignedOf,
    TypeopUnsignedOf,
    TypeopDerefOf,
    TypeopElementOf,
    TypeopTupleHeadOf,
    TypeopTupleTailOf,
    TypeopReturnTypeOf,
    TypeopArgumentsOf,
    TypeopVoidPtrOf,
    TypeopGenericArgsOf,

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
}

impl TryFrom<&str> for LangItemKind {
    type Error = CodeErrorKind;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "slice" => Ok(LangItemKind::Slice),
            "slice_new" => Ok(LangItemKind::SliceNew),
            "slice_const_coerce" => Ok(LangItemKind::SliceConstCoerce),
            "slice_const_cast" => Ok(LangItemKind::SliceConstCast),
            "slice_index" => Ok(LangItemKind::SliceIndex),
            "slice_range_index" => Ok(LangItemKind::SliceRangeIndex),

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
            "proto_any" => Ok(LangItemKind::ProtoAny),
            "proto_array" => Ok(LangItemKind::ProtoArray),
            "proto_tuple" => Ok(LangItemKind::ProtoTuple),
            "proto_range" => Ok(LangItemKind::ProtoRange),
            "proto_named_function" => Ok(LangItemKind::ProtoNamedFunction),
            "proto_function_pointer" => Ok(LangItemKind::ProtoFunctionPointer),
            "proto_callable" => Ok(LangItemKind::ProtoCallable),
            "proto_array_of" => Ok(LangItemKind::ProtoArrayOf),
            "proto_pointer_of" => Ok(LangItemKind::ProtoPointerOf),
            "proto_range_of" => Ok(LangItemKind::ProtoRangeOf),

            // hax
            "proto_iterator" => Ok(LangItemKind::ProtoIterator),

            "builtin_never" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Never)),
            "builtin_void" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Void)),
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

            "typeop_signed_of" => Ok(LangItemKind::TypeopSignedOf),
            "typeop_unsigned_of" => Ok(LangItemKind::TypeopUnsignedOf),
            "typeop_deref_of" => Ok(LangItemKind::TypeopDerefOf),
            "typeop_element_of" => Ok(LangItemKind::TypeopElementOf),
            "typeop_tuple_head_of" => Ok(LangItemKind::TypeopTupleHeadOf),
            "typeop_tuple_tail_of" => Ok(LangItemKind::TypeopTupleTailOf),
            "typeop_return_type_of" => Ok(LangItemKind::TypeopReturnTypeOf),
            "typeop_arguments_of" => Ok(LangItemKind::TypeopArgumentsOf),
            "typeop_void_ptr_of" => Ok(LangItemKind::TypeopVoidPtrOf),
            "typeop_generic_args_of" => Ok(LangItemKind::TypeopGenericArgsOf),

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

            t => {
                if let Some(matches) = regex!(r"^builtin_tuple_(\d+)$").captures(t) {
                    let n = matches[1].parse::<usize>().unwrap();
                    Ok(LangItemKind::ImplTuple(n))
                } else {
                    Err(CodeErrorKind::UnknownLangItem(Some(t.to_string())))
                }
            }
        }
    }
}
