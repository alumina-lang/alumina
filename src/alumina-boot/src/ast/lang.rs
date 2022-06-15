use super::{BinOp, BuiltinType};
use crate::common::CodeErrorKind;
use crate::utils::regex;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItemKind {
    Slice,
    SliceNew,
    SliceIndex,
    SliceRangeIndex,
    SliceCoerce,

    RangeFull,
    RangeFrom,
    RangeTo,
    Range,
    RangeFullNew,
    RangeFromNew,
    RangeToNew,
    RangeNew,

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
    ProtoCallable,
    ProtoNamedFunction,
    ProtoFunctionPointer,
    ProtoAny,
    ProtoArrayOf,
    ProtoPointerOf,

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
    TypeopTupleHeadOf,
    TypeopTupleTailOf,
    TypeopReturnTypeOf,
    TypeopArgumentsOf,

    EntrypointGlue,
    TestCaseMeta,
    TestCaseMetaNew,

    Operator(BinOp),
}

impl TryFrom<&str> for LangItemKind {
    type Error = CodeErrorKind;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "slice" => Ok(LangItemKind::Slice),
            "slice_new" => Ok(LangItemKind::SliceNew),
            "slice_coerce" => Ok(LangItemKind::SliceCoerce),
            "slice_index" => Ok(LangItemKind::SliceIndex),
            "slice_range_index" => Ok(LangItemKind::SliceRangeIndex),

            "range_full" => Ok(LangItemKind::RangeFull),
            "range_from" => Ok(LangItemKind::RangeFrom),
            "range_to" => Ok(LangItemKind::RangeTo),
            "range" => Ok(LangItemKind::Range),

            "range_full_new" => Ok(LangItemKind::RangeFullNew),
            "range_from_new" => Ok(LangItemKind::RangeFromNew),
            "range_to_new" => Ok(LangItemKind::RangeToNew),
            "range_new" => Ok(LangItemKind::RangeNew),

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
            "proto_named_function" => Ok(LangItemKind::ProtoNamedFunction),
            "proto_function_pointer" => Ok(LangItemKind::ProtoFunctionPointer),
            "proto_callable" => Ok(LangItemKind::ProtoCallable),
            "proto_array_of" => Ok(LangItemKind::ProtoArrayOf),
            "proto_pointer_of" => Ok(LangItemKind::ProtoPointerOf),

            // hax
            "proto_iterator" => Ok(LangItemKind::ProtoIterator),

            "impl_never" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Never)),
            "impl_void" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Void)),
            "impl_bool" => Ok(LangItemKind::ImplBuiltin(BuiltinType::Bool)),
            "impl_u8" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U8)),
            "impl_u16" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U16)),
            "impl_u32" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U32)),
            "impl_u64" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U64)),
            "impl_u128" => Ok(LangItemKind::ImplBuiltin(BuiltinType::U128)),
            "impl_usize" => Ok(LangItemKind::ImplBuiltin(BuiltinType::USize)),
            "impl_i8" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I8)),
            "impl_i16" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I16)),
            "impl_i32" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I32)),
            "impl_i64" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I64)),
            "impl_i128" => Ok(LangItemKind::ImplBuiltin(BuiltinType::I128)),
            "impl_isize" => Ok(LangItemKind::ImplBuiltin(BuiltinType::ISize)),
            "impl_f32" => Ok(LangItemKind::ImplBuiltin(BuiltinType::F32)),
            "impl_f64" => Ok(LangItemKind::ImplBuiltin(BuiltinType::F64)),

            "impl_array" => Ok(LangItemKind::ImplArray),

            "operator_eq" => Ok(LangItemKind::Operator(BinOp::Eq)),
            "operator_neq" => Ok(LangItemKind::Operator(BinOp::Neq)),
            "operator_lt" => Ok(LangItemKind::Operator(BinOp::Lt)),
            "operator_lte" => Ok(LangItemKind::Operator(BinOp::LEq)),
            "operator_gt" => Ok(LangItemKind::Operator(BinOp::Gt)),
            "operator_gte" => Ok(LangItemKind::Operator(BinOp::GEq)),

            "typeop_signed_of" => Ok(LangItemKind::TypeopSignedOf),
            "typeop_unsigned_of" => Ok(LangItemKind::TypeopUnsignedOf),
            "typeop_deref_of" => Ok(LangItemKind::TypeopDerefOf),
            "typeop_tuple_head_of" => Ok(LangItemKind::TypeopTupleHeadOf),
            "typeop_tuple_tail_of" => Ok(LangItemKind::TypeopTupleTailOf),
            "typeop_return_type_of" => Ok(LangItemKind::TypeopReturnTypeOf),
            "typeop_arguments_of" => Ok(LangItemKind::TypeopArgumentsOf),

            "entrypoint_glue" => Ok(LangItemKind::EntrypointGlue),
            "test_case_meta" => Ok(LangItemKind::TestCaseMeta),
            "test_case_meta_new" => Ok(LangItemKind::TestCaseMetaNew),

            t => {
                if let Some(matches) = regex!(r"^impl_tuple_(\d+)$").captures(t) {
                    let n = matches[1].parse::<usize>().unwrap();
                    Ok(LangItemKind::ImplTuple(n))
                } else {
                    Err(CodeErrorKind::UnknownLangItem(Some(t.to_string())))
                }
            }
        }
    }
}
