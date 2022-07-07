use super::TyP;

pub enum LangTypeKind<'ir> {
    DynSelf,
    Slice(TyP<'ir>),
    Range(TyP<'ir>),
    Dyn(TyP<'ir>, TyP<'ir>),
}
