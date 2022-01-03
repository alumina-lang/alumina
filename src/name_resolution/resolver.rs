use crate::{
    ast::Ty,
    common::{CodeErrorKind, CycleGuardian},
    name_resolution::{path::Path, scope::NamedItemKind},
};

use super::{
    path::PathSegment,
    scope::{NamedItem, Scope, ScopeInner},
};

pub struct NameResolver<'ast, 'src> {
    cycle_guardian: CycleGuardian<(u32, *const ScopeInner<'ast, 'src>, Path<'ast>)>,
}

#[derive(Debug)]
pub enum ScopeResolution<'ast, 'src> {
    Scope(Scope<'ast, 'src>),
    // Defered scope resolution is used where we cannot determine the item type during
    // the first pass, e.g. when resolving a T::associated_fn where T is not monomorphized yet,
    // but also to be able to resolve mixin methods, enum members and other type-associated
    // items (type is TBD).
    Defered(Ty<'ast>),
}

#[derive(Debug)]
pub enum ItemResolution<'ast, 'src> {
    Item(NamedItem<'ast, 'src>),
    Defered(Ty<'ast>, PathSegment<'ast>),
}

impl<'ast, 'src> NameResolver<'ast, 'src> {
    pub fn new() -> Self {
        NameResolver {
            cycle_guardian: CycleGuardian::new(),
        }
    }

    pub fn resolve_scope(
        &mut self,
        self_scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ScopeResolution<'ast, 'src>, CodeErrorKind> {
        let _guard = self
            .cycle_guardian
            .guard((1, self_scope.0.as_ptr(), path.clone()))
            .map_err(|_| CodeErrorKind::CycleDetected)?;

        if path.absolute {
            return self.resolve_scope(
                self_scope.find_root(),
                Path {
                    absolute: false,
                    segments: path.segments.clone(),
                },
            );
        }

        if path.segments.is_empty() {
            return Ok(ScopeResolution::Scope(self_scope));
        }

        let remainder = Path {
            absolute: false,
            segments: path.segments[1..].to_vec(),
        };

        for item in self_scope.inner().items_with_name(path.segments[0].0) {
            match &item.kind {
                NamedItemKind::Placeholder(sym, _) if path.segments.len() == 1 => {
                    return Ok(ScopeResolution::Defered(Ty::Placeholder(*sym)))
                }
                NamedItemKind::Type(item, _, _) if path.segments.len() == 1 => {
                    return Ok(ScopeResolution::Defered(Ty::NamedType(item)))
                }
                NamedItemKind::Module(child_scope) => {
                    return self.resolve_scope(child_scope.clone(), remainder);
                }
                NamedItemKind::Alias(target) => {
                    return self.resolve_scope(self_scope.clone(), target.join_with(remainder));
                }
                _ => {}
            }
        }

        if let Some(parent) = self_scope.parent() {
            return self.resolve_scope(parent, path);
        }

        Err(CodeErrorKind::UnresolvedPath(path.to_string()))
    }

    pub fn resolve_item(
        &mut self,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ItemResolution<'ast, 'src>, CodeErrorKind> {
        self.resolve_item_impl(scope.clone(), scope, path)
    }

    fn resolve_item_impl(
        &mut self,
        self_scope: Scope<'ast, 'src>,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ItemResolution<'ast, 'src>, CodeErrorKind> {
        let _guard = self
            .cycle_guardian
            .guard((1, scope.0.as_ptr(), path.clone()))
            .map_err(|_| CodeErrorKind::CycleDetected)?;

        if path.segments.is_empty() {
            return Err(CodeErrorKind::UnresolvedPath(path.to_string()));
        }

        let last_segment = path.segments.last().unwrap();

        let containing_scope = match self.resolve_scope(scope.clone(), path.pop())? {
            ScopeResolution::Scope(scope) => scope,
            ScopeResolution::Defered(symbol) => {
                return Ok(ItemResolution::Defered(symbol, last_segment.clone()))
            }
        };

        for item in containing_scope
            .inner()
            .items_with_name(path.segments.last().unwrap().0)
        {
            match &item.kind {
                NamedItemKind::Impl(_, _) => continue,
                NamedItemKind::Alias(target) => {
                    return self.resolve_item_impl(
                        self_scope,
                        containing_scope.clone(),
                        target.clone(),
                    );
                }
                NamedItemKind::Macro(_, _, _)
                | NamedItemKind::Local(_)
                | NamedItemKind::Parameter(..) => {
                    let original_func = self_scope.find_containing_function();
                    let current_func = containing_scope.find_containing_function();

                    if current_func.is_none() || (original_func == current_func) {
                        return Ok(ItemResolution::Item(item.clone()));
                    } else {
                        return Err(CodeErrorKind::CannotReferenceLocal(path.to_string()));
                    }
                }
                _ => return Ok(ItemResolution::Item(item.clone())),
            }
        }

        if containing_scope == scope {
            if let Some(parent) = scope.parent() {
                return self.resolve_item_impl(self_scope, parent, path);
            }
        }

        Err(CodeErrorKind::UnresolvedPath(path.to_string()))
    }
}
