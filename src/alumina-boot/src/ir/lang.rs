use crate::ir::TyP;

pub enum LangTypeKind<'ir> {
    DynSelf,
    Slice(TyP<'ir>),
    Range(TyP<'ir>),
    Dyn(TyP<'ir>, TyP<'ir>),
    ProtoCallable(&'ir [TyP<'ir>], TyP<'ir>),
}
