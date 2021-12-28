use once_cell::sync::OnceCell;
use std::collections::HashMap;

use crate::common::CodeErrorKind;

use super::ItemP;

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
    ProtoPointer,
    ProtoAny,

    ImplBool,
    ImplU8,
    ImplU16,
    ImplU32,
    ImplU64,
    ImplU128,
    ImplUsize,
    ImplI8,
    ImplI16,
    ImplI32,
    ImplI64,
    ImplI128,
    ImplIsize,
    ImplF32,
    ImplF64,
}

pub fn lang_item_kind(name: &str) -> Option<LangItemKind> {
    static MAP: OnceCell<HashMap<&'static str, LangItemKind>> = OnceCell::new();
    MAP.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("lang(slice)", LangItemKind::Slice);
        map.insert("lang(slice_new)", LangItemKind::SliceNew);
        map.insert("lang(slice_coerce)", LangItemKind::SliceCoerce);
        map.insert("lang(slice_index)", LangItemKind::SliceIndex);
        map.insert("lang(slice_range_index)", LangItemKind::SliceRangeIndex);
        map.insert(
            "lang(slice_range_index_lower)",
            LangItemKind::SliceRangeIndexLower,
        );
        map.insert("lang(proto_primitive)", LangItemKind::ProtoPrimitive);
        map.insert("lang(proto_numeric)", LangItemKind::ProtoNumeric);
        map.insert("lang(proto_integer)", LangItemKind::ProtoInteger);
        map.insert(
            "lang(proto_floating_point)",
            LangItemKind::ProtoFloatingPoint,
        );
        map.insert("lang(proto_signed)", LangItemKind::ProtoSigned);
        map.insert("lang(proto_unsigned)", LangItemKind::ProtoUnsigned);
        map.insert("lang(proto_pointer)", LangItemKind::ProtoPointer);
        map.insert("lang(proto_any)", LangItemKind::ProtoAny);
        map.insert("lang(impl_bool)", LangItemKind::ImplBool);
        map.insert("lang(impl_u8)", LangItemKind::ImplU8);
        map.insert("lang(impl_u16)", LangItemKind::ImplU16);
        map.insert("lang(impl_u32)", LangItemKind::ImplU32);
        map.insert("lang(impl_u64)", LangItemKind::ImplU64);
        map.insert("lang(impl_u128)", LangItemKind::ImplU128);
        map.insert("lang(impl_usize)", LangItemKind::ImplUsize);
        map.insert("lang(impl_i8)", LangItemKind::ImplI8);
        map.insert("lang(impl_i16)", LangItemKind::ImplI16);
        map.insert("lang(impl_i32)", LangItemKind::ImplI32);
        map.insert("lang(impl_i64)", LangItemKind::ImplI64);
        map.insert("lang(impl_i128)", LangItemKind::ImplI128);
        map.insert("lang(impl_isize)", LangItemKind::ImplIsize);
        map.insert("lang(impl_f32)", LangItemKind::ImplF32);
        map.insert("lang(impl_f64)", LangItemKind::ImplF64);
        map
    })
    .get(name)
    .copied()
}
