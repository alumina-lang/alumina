use crate::{
    common::AluminaError,
    name_resolution::{path::Path, scope::Item},
};
use std::collections::HashSet;

use super::scope::{Scope, ScopeInner};

pub struct NameResolver<'gcx, 'src> {
    seen_aliases: HashSet<(u32, *const ScopeInner<'gcx, 'src>, Path<'src>)>,
}

impl<'gcx, 'src> NameResolver<'gcx, 'src> {
    pub fn new() -> Self {
        NameResolver {
            seen_aliases: HashSet::new(),
        }
    }

    pub fn resolve_scope(
        &mut self,
        scope: Scope<'gcx, 'src>,
        path: &Path<'src>,
    ) -> Result<Scope<'gcx, 'src>, AluminaError> {
        println!("resolve_scope({}, {})", scope.path(), path);

        if !self
            .seen_aliases
            .insert((1, scope.0.as_ptr(), path.clone()))
        {
            return Err(AluminaError::CycleDetected);
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
            return Ok(scope);
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

        Err(AluminaError::UnresolvedPath(path.to_string()))
    }

    pub fn resolve_type_item(
        &mut self,
        scope: Scope<'gcx, 'src>,
        path: &Path<'src>,
    ) -> Result<Item<'gcx, 'src>, AluminaError> {
        println!("resolve_type_item({}, {})", scope.path(), path);

        if !self
            .seen_aliases
            .insert((2, scope.0.as_ptr(), path.clone()))
        {
            return Err(AluminaError::CycleDetected);
        }

        if path.segments.is_empty() {
            return Err(AluminaError::UnresolvedPath(path.to_string()));
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
                    return Ok(item.clone());
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

        Err(AluminaError::UnresolvedPath(path.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use std::assert_matches::assert_matches;

    use crate::{
        common::{AluminaError, SyntaxError},
        context::GlobalCtx,
        name_resolution::scope::{Item, Scope, ScopeType},
        parser::ParseCtx,
        types::{Ty, TyP},
        visitors::{pass1::FirstPassVisitor, types::TypeVisitor},
    };

    use crate::parser::AluminaVisitor;

    trait AsTyP<'gcx> {
        fn as_typ(self, ctx: &'gcx GlobalCtx<'gcx>) -> TyP<'gcx>;
    }

    impl<'gcx> AsTyP<'gcx> for Ty<'gcx> {
        fn as_typ(self, ctx: &'gcx GlobalCtx<'gcx>) -> TyP<'gcx> {
            ctx.intern(self)
        }
    }

    fn first_pass<'gcx, 'src>(
        parse_ctx: &'src ParseCtx<'gcx, 'src>,
    ) -> Result<Scope<'gcx, 'src>, SyntaxError<'src>> {
        let root_scope = Scope::new_root();

        let module_scope =
            root_scope.new_child_with_parse_ctx(ScopeType::Crate, "test", parse_ctx.to_owned());

        root_scope
            .add_item("test", Item::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(module_scope);
        visitor.visit(parse_ctx.root_node())?;

        Ok(root_scope)
    }

    fn extract_type<'gcx, 'src>(
        root_scope: Scope<'gcx, 'src>,
    ) -> Result<TyP<'gcx>, SyntaxError<'src>> {
        let (scope, node) = match &(*root_scope.0).borrow().items["test"][..] {
            [Item::Module(scope)] => match &(*scope.0).borrow().items["a"][..] {
                [Item::Type(_, _, scope)] => match &(*scope.0).borrow().items["b"][..] {
                    [Item::Field(_, node)] => {
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
        let ctx = GlobalCtx::new();
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

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_referenced_type_super() {
        let ctx = GlobalCtx::new();
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

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_infinite_loop() {
        let ctx = GlobalCtx::new();
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
        let ctx = GlobalCtx::new();
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

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_referenced_type_absolute() {
        let ctx = GlobalCtx::new();
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

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }
}
