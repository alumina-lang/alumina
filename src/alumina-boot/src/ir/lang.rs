use super::TyP;

pub enum LangTypeKind<'ir> {
    Slice(TyP<'ir>),
}
