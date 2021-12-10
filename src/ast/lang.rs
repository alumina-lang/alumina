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
    SliceConst,
    MakeSliceConst,
    SliceMut,
    MakeSliceMut,
    SliceEqual,
    SliceCoerce,
}

pub fn lang_item_kind(name: &str) -> Option<LangItemKind> {
    static MAP: OnceCell<HashMap<&'static str, LangItemKind>> = OnceCell::new();
    MAP.get_or_init(|| {
        let mut map = HashMap::new();
        map.insert("lang(slice_const)", LangItemKind::SliceConst);
        map.insert("lang(make_slice_const)", LangItemKind::MakeSliceConst);
        map.insert("lang(slice_mut)", LangItemKind::SliceMut);
        map.insert("lang(make_slice_mut)", LangItemKind::MakeSliceMut);
        map.insert("lang(slice_equal)", LangItemKind::SliceEqual);
        map.insert("lang(slice_coerce)", LangItemKind::SliceCoerce);
        map
    })
    .get(name)
    .copied()
}
