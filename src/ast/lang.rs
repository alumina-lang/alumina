use once_cell::sync::OnceCell;
use std::collections::HashMap;

use crate::common::AluminaErrorKind;

use super::ItemP;

pub struct LangItemMap<'ast>(HashMap<LangItemKind, ItemP<'ast>>);

impl<'ast> LangItemMap<'ast> {
    pub fn new(inner: HashMap<LangItemKind, ItemP<'ast>>) -> Self {
        Self(inner)
    }

    pub fn get(&self, kind: LangItemKind) -> Result<ItemP<'ast>, AluminaErrorKind> {
        self.0
            .get(&kind)
            .copied()
            .ok_or_else(|| AluminaErrorKind::MissingLangItem(kind))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItemKind {
    Slice,
    SliceNew,
    SliceEqual,
    SliceIndex,
    SliceRangeIndex,
    SliceRangeIndexLower,
    SliceCoerce,
}

pub fn lang_item_kind(name: &str) -> Option<LangItemKind> {
    static MAP: OnceCell<HashMap<&'static str, LangItemKind>> = OnceCell::new();
    MAP.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("lang(slice)", LangItemKind::Slice);
        map.insert("lang(slice_new)", LangItemKind::SliceNew);
        map.insert("lang(slice_equal)", LangItemKind::SliceEqual);
        map.insert("lang(slice_coerce)", LangItemKind::SliceCoerce);
        map.insert("lang(slice_index)", LangItemKind::SliceIndex);
        map.insert("lang(slice_range_index)", LangItemKind::SliceRangeIndex);
        map.insert(
            "lang(slice_range_index_lower)",
            LangItemKind::SliceRangeIndexLower,
        );
        map
    })
    .get(name)
    .copied()
}
