use crate::{
    ast::AstId,
    common::{AluminaError, AluminaErrorKind},
    name_resolution::{path::Path, scope::NamedItem},
    parser::ParseCtx,
};
use std::collections::HashSet;

use super::{
    path::PathSegment,
    scope::{Scope, ScopeInner, ScopeType},
};

pub struct NameResolver<'ast, 'src> {
    seen_aliases: HashSet<(u32, *const ScopeInner<'ast, 'src>, Path<'ast>)>,
    depth: usize,
}

#[derive(Debug)]
pub enum ScopeResolution<'ast, 'src> {
    Scope(Scope<'ast, 'src>),
    // It could happen that path is something like T::associated_fn where T
    // is a generic placeholder. In this case we cannot statically resolve the path yet
    // and we need to defer until monomorphization time.
    Defered(AstId),
}

#[derive(Debug)]
pub enum ItemResolution<'ast, 'src> {
    Item(NamedItem<'ast, 'src>),
    // Only a single path segment can follow a placeholder (and it has to be an associated function)
    // as we don't support nested structs.
    Defered(AstId, PathSegment<'ast>),
}

impl<'ast, 'src> NameResolver<'ast, 'src> {
    pub fn new() -> Self {
        NameResolver {
            seen_aliases: HashSet::new(),
            depth: 0,
        }
    }

    pub fn resolve_scope(
        &mut self,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ScopeResolution<'ast, 'src>, AluminaErrorKind> {
        if !self
            .seen_aliases
            .insert((1, scope.0.as_ptr(), path.clone()))
        {
            return Err(AluminaErrorKind::CycleDetected);
        }

        if path.absolute {
            return self.resolve_scope(
                scope.find_root(),
                Path {
                    absolute: false,
                    segments: path.segments.clone(),
                },
            );
        }

        if path.segments.is_empty() {
            return Ok(ScopeResolution::Scope(scope));
        }

        let remainder = Path {
            absolute: false,
            segments: path.segments[1..].to_vec(),
        };

        for item in scope.inner().items_with_name(path.segments[0].0) {
            match item {
                NamedItem::Placeholder(sym) => return Ok(ScopeResolution::Defered(*sym)),
                NamedItem::Module(child_scope) | NamedItem::Impl(child_scope) => {
                    return self.resolve_scope(child_scope.clone(), remainder);
                }
                NamedItem::Type(_, _, scope) if scope.typ() == ScopeType::Enum => {
                    return self.resolve_scope(scope.clone(), remainder);
                }
                NamedItem::Alias(target) => {
                    return self.resolve_scope(scope.clone(), target.join_with(remainder));
                }
                _ => {}
            }
        }

        if let Some(parent) = scope.parent() {
            return self.resolve_scope(parent, path);
        }

        Err(AluminaErrorKind::UnresolvedPath(path.to_string()))
    }

    pub fn resolve_item(
        &mut self,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ItemResolution<'ast, 'src>, AluminaErrorKind> {
        self.resolve_item_impl(scope.clone(), scope, path)
    }

    fn resolve_item_impl(
        &mut self,
        original_scope: Scope<'ast, 'src>,
        scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ItemResolution<'ast, 'src>, AluminaErrorKind> {
        if !self
            .seen_aliases
            .insert((2, scope.0.as_ptr(), path.clone()))
        {
            return Err(AluminaErrorKind::CycleDetected);
        }

        if path.segments.is_empty() {
            return Err(AluminaErrorKind::UnresolvedPath(path.to_string()));
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
            match item {
                NamedItem::Impl(_) => continue,
                NamedItem::Alias(target) => {
                    return self.resolve_item_impl(
                        original_scope,
                        containing_scope.clone(),
                        target.clone(),
                    );
                }
                NamedItem::Local(_) | NamedItem::Parameter(..) => {
                    let original_func = original_scope.find_containing_function();
                    let current_func = containing_scope.find_containing_function();

                    if original_func == current_func {
                        return Ok(ItemResolution::Item(item.clone()));
                    } else {
                        return Err(AluminaErrorKind::CannotReferenceLocal(path.to_string()));
                    }
                }
                _ => return Ok(ItemResolution::Item(item.clone())),
            }
        }

        // If path was already absolute, no sense in trying to resolve it again
        // in parent scope.
        if !path.absolute {
            if let Some(parent) = scope.parent() {
                return self.resolve_item_impl(original_scope, parent, path);
            }
        }

        Err(AluminaErrorKind::UnresolvedPath(path.to_string()))
    }
}
