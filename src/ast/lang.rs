use once_cell::sync::OnceCell;
use regex::Regex;
use std::collections::HashMap;

use crate::common::CodeErrorKind;

use super::{BinOp, BuiltinType, ItemP};

pub struct LangItemMap<'ast>(HashMap<LangItemKind, ItemP<'ast>>);

impl<'ast> LangItemMap<'ast> {
    pub fn new(inner: HashMap<LangItemKind, ItemP<'ast>>) -> Self {
        Self(inner)
    }

    pub fn get(&self, kind: LangItemKind) -> Result<ItemP<'ast>, CodeErrorKind> {
        self.0
            .get(&kind)
            .copied()
            .ok_or(CodeErrorKind::MissingLangItem(kind))
    }

    pub fn reverse_get(&self, item: ItemP<'ast>) -> Option<LangItemKind> {
        self.0
            .iter()
            .find(|(_, v)| **v == item)
            .map(|(k, _)| k)
            .copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItemKind {
    Slice,
    SliceNew,
    SliceIndex,
    SliceRangeIndex,
    SliceRangeIndexLower,
    SliceCoerce,

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
    ProtoAny,
    ProtoArrayOf,
    ProtoPointerOf,

    ImplBuiltin(BuiltinType),
    ImplTuple(usize),
    ImplArray,

    Operator(BinOp),
}

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: once_cell::sync::OnceCell<regex::Regex> = once_cell::sync::OnceCell::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

pub fn lang_item_kind(name: &str) -> Option<LangItemKind> {
    match name {
        "lang(slice)" => Some(LangItemKind::Slice),
        "lang(slice_new)" => Some(LangItemKind::SliceNew),
        "lang(slice_coerce)" => Some(LangItemKind::SliceCoerce),
        "lang(slice_index)" => Some(LangItemKind::SliceIndex),
        "lang(slice_range_index)" => Some(LangItemKind::SliceRangeIndex),
        "lang(slice_range_index_lower)" => Some(LangItemKind::SliceRangeIndexLower),
        "lang(proto_primitive)" => Some(LangItemKind::ProtoPrimitive),
        "lang(proto_numeric)" => Some(LangItemKind::ProtoNumeric),
        "lang(proto_integer)" => Some(LangItemKind::ProtoInteger),
        "lang(proto_floating_point)" => Some(LangItemKind::ProtoFloatingPoint),
        "lang(proto_signed)" => Some(LangItemKind::ProtoSigned),
        "lang(proto_unsigned)" => Some(LangItemKind::ProtoUnsigned),
        "lang(proto_pointer)" => Some(LangItemKind::ProtoPointer),
        "lang(proto_zero_sized)" => Some(LangItemKind::ProtoZeroSized),
        "lang(proto_any)" => Some(LangItemKind::ProtoAny),
        "lang(proto_array)" => Some(LangItemKind::ProtoArray),
        "lang(proto_tuple)" => Some(LangItemKind::ProtoTuple),
        "lang(proto_callable)" => Some(LangItemKind::ProtoCallable),
        "lang(proto_array_of)" => Some(LangItemKind::ProtoArrayOf),
        "lang(proto_pointer_of)" => Some(LangItemKind::ProtoPointerOf),

        "lang(impl_never)" => Some(LangItemKind::ImplBuiltin(BuiltinType::Never)),
        "lang(impl_void)" => Some(LangItemKind::ImplBuiltin(BuiltinType::Void)),
        "lang(impl_bool)" => Some(LangItemKind::ImplBuiltin(BuiltinType::Bool)),
        "lang(impl_u8)" => Some(LangItemKind::ImplBuiltin(BuiltinType::U8)),
        "lang(impl_u16)" => Some(LangItemKind::ImplBuiltin(BuiltinType::U16)),
        "lang(impl_u32)" => Some(LangItemKind::ImplBuiltin(BuiltinType::U32)),
        "lang(impl_u64)" => Some(LangItemKind::ImplBuiltin(BuiltinType::U64)),
        "lang(impl_u128)" => Some(LangItemKind::ImplBuiltin(BuiltinType::U128)),
        "lang(impl_usize)" => Some(LangItemKind::ImplBuiltin(BuiltinType::USize)),
        "lang(impl_i8)" => Some(LangItemKind::ImplBuiltin(BuiltinType::I8)),
        "lang(impl_i16)" => Some(LangItemKind::ImplBuiltin(BuiltinType::I16)),
        "lang(impl_i32)" => Some(LangItemKind::ImplBuiltin(BuiltinType::I32)),
        "lang(impl_i64)" => Some(LangItemKind::ImplBuiltin(BuiltinType::I64)),
        "lang(impl_i128)" => Some(LangItemKind::ImplBuiltin(BuiltinType::I128)),
        "lang(impl_isize)" => Some(LangItemKind::ImplBuiltin(BuiltinType::ISize)),
        "lang(impl_f32)" => Some(LangItemKind::ImplBuiltin(BuiltinType::F32)),
        "lang(impl_f64)" => Some(LangItemKind::ImplBuiltin(BuiltinType::F64)),

        "lang(impl_array)" => Some(LangItemKind::ImplArray),

        "lang(operator_eq)" => Some(LangItemKind::Operator(BinOp::Eq)),
        "lang(operator_neq)" => Some(LangItemKind::Operator(BinOp::Neq)),
        "lang(operator_lt)" => Some(LangItemKind::Operator(BinOp::Lt)),
        "lang(operator_lte)" => Some(LangItemKind::Operator(BinOp::LEq)),
        "lang(operator_gt)" => Some(LangItemKind::Operator(BinOp::Gt)),
        "lang(operator_gte)" => Some(LangItemKind::Operator(BinOp::GEq)),

        t => {
            if let Some(matches) = regex!(r"^lang\(impl_tuple_(\d+)\)$").captures(t) {
                let n = matches[1].parse::<usize>().unwrap();
                Some(LangItemKind::ImplTuple(n))
            } else {
                None
            }
        }
    }
}
