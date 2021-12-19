use crate::{
    ast::{AstId, ItemP},
    common::CodeErrorKind,
    name_resolution::{path::Path, scope::NamedItem},
};
use std::collections::HashSet;

use super::{
    path::PathSegment,
    scope::{Scope, ScopeInner, ScopeType},
};

pub struct NameResolver<'ast, 'src> {
    seen_aliases: HashSet<(u32, *const ScopeInner<'ast, 'src>, Path<'ast>)>,
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
    Defered(AstId, PathSegment<'ast>),
}

impl<'ast, 'src> NameResolver<'ast, 'src> {
    pub fn new() -> Self {
        NameResolver {
            seen_aliases: HashSet::new(),
        }
    }

    pub fn resolve_scope(
        &mut self,
        self_scope: Scope<'ast, 'src>,
        path: Path<'ast>,
    ) -> Result<ScopeResolution<'ast, 'src>, CodeErrorKind> {
        if !self
            .seen_aliases
            .insert((1, self_scope.0.as_ptr(), path.clone()))
        {
            return Err(CodeErrorKind::CycleDetected);
        }

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
            match item {
                NamedItem::Placeholder(sym, _) => return Ok(ScopeResolution::Defered(*sym)),
                NamedItem::Module(child_scope) | NamedItem::Impl(_, child_scope) => {
                    return self.resolve_scope(child_scope.clone(), remainder);
                }
                NamedItem::Type(_, _, scope) if scope.typ() == ScopeType::Enum => {
                    return self.resolve_scope(scope.clone(), remainder);
                }
                NamedItem::Alias(target) => {
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
        if !self
            .seen_aliases
            .insert((2, scope.0.as_ptr(), path.clone()))
        {
            return Err(CodeErrorKind::CycleDetected);
        }

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
            match item {
                NamedItem::Impl(_, _) => continue,
                NamedItem::Alias(target) => {
                    return self.resolve_item_impl(
                        self_scope,
                        containing_scope.clone(),
                        target.clone(),
                    );
                }
                NamedItem::Macro(_, _, _) | NamedItem::Local(_) | NamedItem::Parameter(..) => {
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
