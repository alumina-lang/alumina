use std::collections::HashSet;

use crate::name_resolution::{path::Path, scope::Item};

use super::scope::{Scope, ScopeInner};

pub struct NameResolver<'tcx> {
    seen_aliases: HashSet<(u32, *const ScopeInner<'tcx>, Path<'tcx>)>,
}

impl<'tcx> NameResolver<'tcx> {
    pub fn new() -> Self {
        NameResolver {
            seen_aliases: HashSet::new(),
        }
    }

    pub fn resolve_scope(&mut self, scope: Scope<'tcx>, path: &Path<'tcx>) -> Option<Scope<'tcx>> {
        println!("resolve_scope({}, {})", scope.path(), path);

        if !self
            .seen_aliases
            .insert((1, scope.0.as_ptr(), path.clone()))
        {
            return None;
        }

        if path.absolute {
            return self.resolve_scope(
                scope.find_root(),
                &Path {
                    absolute: false,
                    segments: path.segments.clone(),
                },
            );
        }

        if path.segments.is_empty() {
            return Some(scope);
        }

        let remainder = Path {
            absolute: false,
            segments: path.segments[1..].to_vec(),
        };

        let inner = scope.0.borrow();
        for item in inner
            .items
            .get(path.segments[0].0)
            .iter()
            .flat_map(|u| u.iter())
        {
            match item {
                Item::Module(child_scope) | Item::Impl(child_scope) => {
                    return self.resolve_scope(child_scope.clone(), &remainder);
                }
                Item::Alias(target) => {
                    return self.resolve_scope(scope.clone(), &target.join_with(remainder));
                }
                _ => {}
            }
        }

        if let Some(parent) = scope.parent() {
            return self.resolve_scope(parent, path);
        }

        None
    }

    pub fn resolve_type_item(
        &mut self,
        scope: Scope<'tcx>,
        path: &Path<'tcx>,
    ) -> Option<Item<'tcx>> {
        println!("resolve_type_item({}, {})", scope.path(), path);

        if !self
            .seen_aliases
            .insert((2, scope.0.as_ptr(), path.clone()))
        {
            return None;
        }

        if path.segments.is_empty() {
            return None;
        }

        let containing_scope = self.resolve_scope(scope.clone(), &path.pop())?;

        let inner = containing_scope.0.borrow();
        for item in inner
            .items
            .get(path.segments.last().unwrap().0)
            .iter()
            .flat_map(|u| u.iter())
        {
            match item {
                Item::Type(_, _, _) | Item::Placeholder(_) => {
                    return Some(item.clone());
                }
                Item::Alias(target) => {
                    return self.resolve_type_item(containing_scope.clone(), target);
                }
                _ => {}
            }
        }

        if let Some(parent) = scope.parent() {
            return self.resolve_type_item(parent, path);
        }

        None
    }
}
