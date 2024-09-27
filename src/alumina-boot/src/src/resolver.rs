use crate::ast::Ty;
use crate::common::{CodeDiagnostic, CycleGuardian};
use crate::src::path::{Path, PathSegment};
use crate::src::scope::{NamedItem, NamedItemKind, Scope, ScopeInner};

pub struct NameResolver<'ast, 'src> {
    cycle_guardian: CycleGuardian<(u32, *const ScopeInner<'ast, 'src>, Path<'ast>)>,
}

#[derive(Debug)]
pub enum ScopeResolution<'ast, 'src> {
    Scope(Scope<'ast, 'src>),
    // Defered scope resolution is used where we cannot determine the item type during
    // the first pass, e.g. when resolving a T is:associated_fn where T is not monomorphized yet,
    // but also to be able to resolve mixin methods, enum members and other type-associated
    // items (type is TBD).
    Defered(Ty<'ast>),
}

#[derive(Debug)]
pub enum ItemResolution<'ast, 'src> {
    Item(NamedItem<'ast, 'src>),
    Defered(Ty<'ast>, PathSegment<'ast>),
}

// Name resolution has the following order:
// - explicitely named items and imports in each scope (including aliases, i.e. use foo::bar::X as Y;)
// - star imports (use foo::bar::*;)
// - items in parent scope
// As star imports are weaker than explicit imports, that allows local definitions to shadow them.
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
    ) -> Result<ScopeResolution<'ast, 'src>, CodeDiagnostic> {
        let _guard = self
            .cycle_guardian
            .guard((1, self_scope.0.as_ptr(), path.clone()))
            .map_err(|_| CodeDiagnostic::CycleDetected)?;

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

        let mut result = None;
        for item in self_scope.inner().items_with_name(path.segments[0].0) {
            match &item.kind {
                NamedItemKind::Placeholder(sym) if path.segments.len() == 1 => {
                    result = Some(Ok(ScopeResolution::Defered(Ty::Placeholder(*sym))));
                    break;
                }
                NamedItemKind::Type(item) if path.segments.len() == 1 => {
                    result = Some(Ok(ScopeResolution::Defered(Ty::Item(item))));
                    break;
                }
                NamedItemKind::TypeDef(item) if path.segments.len() == 1 => {
                    result = Some(Ok(ScopeResolution::Defered(Ty::Item(item))));
                    break;
                }
                NamedItemKind::Protocol(_) => {
                    result =
                        Some(self.resolve_scope(item.scope.as_ref().unwrap().clone(), remainder));
                    break;
                }
                NamedItemKind::Module => {
                    result =
                        Some(self.resolve_scope(item.scope.as_ref().unwrap().clone(), remainder));
                    break;
                }
                NamedItemKind::Alias(target) => {
                    result =
                        Some(self.resolve_scope(self_scope.clone(), target.join_with(remainder)));
                    break;
                }
                _ => {}
            }
        }

        if let Some(result) = result {
            self_scope.mark_used(path.segments[0].0);
            return result;
        }

        for import in self_scope.inner().star_imports() {
            match self.resolve_scope(self_scope.clone(), import.clone()) {
                Ok(ScopeResolution::Scope(scope)) => {
                    match self.resolve_scope(scope, path.clone()) {
                        Ok(item) => return Ok(item),
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        if let Some(parent) = self_scope.parent() {
            return self.resolve_scope(parent, path);
        }

        Err(CodeDiagnostic::UnresolvedPath(path.to_string()))
    }

    pub fn resolve_item(
        &mut self,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ItemResolution<'ast, 'src>, CodeDiagnostic> {
        self.resolve_item_impl(scope.clone(), scope, path, true)
    }

    fn resolve_item_impl(
        &mut self,
        self_scope: Scope<'ast, 'src>,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
        go_down: bool,
    ) -> Result<ItemResolution<'ast, 'src>, CodeDiagnostic> {
        let _guard = self
            .cycle_guardian
            .guard((1, scope.0.as_ptr(), path.clone()))
            .map_err(|_| CodeDiagnostic::CycleDetected)?;

        if path.segments.is_empty() {
            return Err(CodeDiagnostic::UnresolvedPath(path.to_string()));
        }

        let last_segment = path.segments.last().unwrap();

        let containing_scope = match self.resolve_scope(scope.clone(), path.pop())? {
            ScopeResolution::Scope(scope) => scope,
            ScopeResolution::Defered(symbol) => {
                return Ok(ItemResolution::Defered(symbol, last_segment.clone()))
            }
        };

        let mut result = None;
        for item in containing_scope.inner().items_with_name(last_segment.0) {
            match &item.kind {
                NamedItemKind::Impl => continue,
                NamedItemKind::Alias(target) => {
                    result = Some(self.resolve_item_impl(
                        self_scope.clone(),
                        containing_scope.clone(),
                        target.clone(),
                        true,
                    ));
                    break;
                }
                NamedItemKind::Macro(_)
                | NamedItemKind::Local(_)
                | NamedItemKind::Parameter(_)
                | NamedItemKind::BoundValue(_, _, _) => {
                    let original_func = self_scope.find_containing_function();
                    let current_func = containing_scope.find_containing_function();

                    if current_func.is_none() || (original_func == current_func) {
                        result = Some(Ok(ItemResolution::Item(item.clone())));
                        break;
                    } else {
                        return Err(CodeDiagnostic::CannotReferenceLocal(path.to_string()));
                    }
                }
                _ => {
                    result = Some(Ok(ItemResolution::Item(item.clone())));
                    break;
                }
            }
        }

        if let Some(result) = result {
            containing_scope.mark_used(last_segment.0);
            return result;
        }

        for import in containing_scope.inner().star_imports() {
            match self.resolve_scope(scope.clone(), import.clone()) {
                Ok(ScopeResolution::Scope(scope)) => match self.resolve_item_impl(
                    self_scope.clone(),
                    scope,
                    last_segment.clone().into(),
                    false,
                ) {
                    Ok(item) => return Ok(item),
                    _ => {}
                },
                _ => {}
            }
        }

        if go_down && containing_scope == scope {
            if let Some(parent) = scope.parent() {
                return self.resolve_item_impl(self_scope, parent, path, true);
            }
        }

        Err(CodeDiagnostic::UnresolvedPath(path.to_string()))
    }
}
