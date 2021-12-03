use crate::{
    ast::AstId,
    common::AluminaError,
    name_resolution::{path::Path, scope::NamedItem},
};
use std::collections::HashSet;

use super::{
    path::PathSegment,
    scope::{Scope, ScopeInner},
};

pub struct NameResolver<'ast, 'src> {
    seen_aliases: HashSet<(u32, *const ScopeInner<'ast, 'src>, Path<'src>)>,
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
    Defered(AstId, PathSegment<'src>),
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
        path: Path<'src>,
    ) -> Result<ScopeResolution<'ast, 'src>, AluminaError> {
        println!(
            "resolve_scope({:?} {:?}, {})",
            scope.inner().r#type,
            scope.path(),
            path
        );

        if !self
            .seen_aliases
            .insert((1, scope.0.as_ptr(), path.clone()))
        {
            return Err(AluminaError::CycleDetected);
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
                NamedItem::Alias(target) => {
                    return self.resolve_scope(scope.clone(), target.join_with(remainder));
                }
                _ => {}
            }
        }

        if let Some(parent) = scope.parent() {
            return self.resolve_scope(parent, path);
        }

        Err(AluminaError::UnresolvedPath(path.to_string()))
    }

    pub fn resolve_item(
        &mut self,
        scope: Scope<'ast, 'src>,
        path: Path<'src>,
    ) -> Result<ItemResolution<'ast, 'src>, AluminaError> {
        println!(
            "resolve_item({:?} {:?}, {})",
            scope.inner().r#type,
            scope.path(),
            path
        );

        if !self
            .seen_aliases
            .insert((2, scope.0.as_ptr(), path.clone()))
        {
            return Err(AluminaError::CycleDetected);
        }

        if path.segments.is_empty() {
            return Err(AluminaError::UnresolvedPath(path.to_string()));
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
                    return self.resolve_item(containing_scope.clone(), target.clone());
                }
                _ => return Ok(ItemResolution::Item(item.clone())),
            }
        }

        // If path was already absolute, no sense in trying to resolve it again
        // in parent scope.
        if !path.absolute {
            if let Some(parent) = scope.parent() {
                return self.resolve_item(parent, path);
            }
        }

        Err(AluminaError::UnresolvedPath(path.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use std::assert_matches::assert_matches;

    use crate::{
        ast::{Ty, TyP},
        common::{AluminaError, SyntaxError},
        context::AstCtx,
        name_resolution::scope::{NamedItem, Scope, ScopeType},
        parser::ParseCtx,
        visitors::{pass1::FirstPassVisitor, types::TypeVisitor},
    };

    use crate::parser::AluminaVisitor;

    fn first_pass<'ast, 'src>(
        parse_ctx: &'src ParseCtx<'ast, 'src>,
    ) -> Result<Scope<'ast, 'src>, SyntaxError<'src>> {
        let root_scope = Scope::new_root();

        let module_scope =
            root_scope.named_child_with_ctx(ScopeType::Crate, "test", parse_ctx.to_owned());

        root_scope
            .add_item("test", NamedItem::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(module_scope);
        visitor.visit(parse_ctx.root_node())?;

        Ok(root_scope)
    }

    fn extract_type<'ast, 'src>(
        root_scope: Scope<'ast, 'src>,
    ) -> Result<TyP<'ast>, SyntaxError<'src>> {
        let (scope, node) = match &(*root_scope.0).borrow().items["test"][..] {
            [NamedItem::Module(scope)] => match &(*scope.0).borrow().items["a"][..] {
                [NamedItem::Type(_, _, scope)] => match &(*scope.0).borrow().items["b"][..] {
                    [NamedItem::Field(node)] => {
                        (scope.clone(), node.child_by_field_name("type").unwrap())
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        let mut visitor = TypeVisitor::new(scope);
        visitor.visit(node)
    }

    #[test]
    fn test_referenced_type() {
        let ctx = AstCtx::new();
        let parse_ctx = ParseCtx::from_source(
            &ctx,
            "
        mod foo {
            struct bar {}
        }

        struct a {
            b: foo::bar,
        }
        ",
        );
        let root_scope = first_pass(&parse_ctx).unwrap();
        let result = extract_type(root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, &Ty::NamedType(symbol));
    }

    #[test]
    fn test_referenced_type_super() {
        let ctx = AstCtx::new();
        let parse_ctx = ParseCtx::from_source(
            &ctx,
            r"
        mod foo {
            mod goo {
                use super::bar;
            }
            struct bar {}
        }

        struct a {
            b: foo::goo::bar,
        }
        ",
        );

        let root_scope = first_pass(&parse_ctx).unwrap();
        let result = extract_type(root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, &Ty::NamedType(symbol));
    }

    #[test]
    fn test_infinite_loop() {
        let ctx = AstCtx::new();
        let parse_ctx = ParseCtx::from_source(
            &ctx,
            r"
        mod foo {
            use super::bar::baz;
        }

        mod bar {
            use super::foo::baz;
        }

        struct a {
            b: foo::baz,
        }
        ",
        );

        let root_scope = first_pass(&parse_ctx).unwrap();
        let err = extract_type(root_scope).unwrap_err();

        assert_matches!(err.kind, AluminaError::CycleDetected);
    }

    #[test]
    fn test_referenced_type_crate() {
        let ctx = AstCtx::new();
        let parse_ctx = ParseCtx::from_source(
            &ctx,
            r"
        mod foo {
            struct bar {}
        }

        struct a {
            b: crate::foo::bar,
        }
        ",
        );

        let root_scope = first_pass(&parse_ctx).unwrap();
        let result = extract_type(root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, &Ty::NamedType(symbol));
    }

    #[test]
    fn test_referenced_type_absolute() {
        let ctx = AstCtx::new();
        let parse_ctx = ParseCtx::from_source(
            &ctx,
            r"
        mod foo {
            struct bar {}
        }

        struct a {
            b: ::test::foo::bar,
        }
        ",
        );

        let root_scope = first_pass(&parse_ctx).unwrap();
        let result = extract_type(root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, &Ty::NamedType(symbol));
    }
}
