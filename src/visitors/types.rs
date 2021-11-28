use crate::AluminaVisitor;
use crate::{
    common::{SyntaxError, ToSyntaxError},
    context::GlobalCtx,
    name_resolution::{
        resolver::NameResolver,
        scope::{Item, Scope},
    },
    types::{BuiltinType, Ty, TyP},
    visitors::ScopedPathVisitor,
};

pub struct TypeVisitor<'tcx> {
    source: &'tcx str,
    global_ctx: &'tcx GlobalCtx<'tcx>,
    scope: Scope<'tcx>,
}

impl<'tcx> TypeVisitor<'tcx> {
    pub fn new(global_ctx: &'tcx GlobalCtx<'tcx>, source: &'tcx str, scope: Scope<'tcx>) -> Self {
        TypeVisitor {
            source,
            global_ctx,
            scope,
        }
    }

    fn visit_typeref(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<TyP<'tcx>, SyntaxError<'tcx>> {
        let mut visitor = ScopedPathVisitor {
            source: self.source,
            scope: self.scope.clone(),
            //global_ctx: self.global_ctx,
        };
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let res = match resolver
            .resolve_type_item(self.scope.clone(), &path)
            .to_syntax_error(node)?
        {
            Item::Type(ty, _, _) => self.global_ctx.intern(Ty::NamedType(ty)),
            Item::Placeholder(ty) => self.global_ctx.intern(Ty::Placeholder(ty)),
            _ => unreachable!(),
        };

        Ok(res)
    }
}

impl<'tcx> AluminaVisitor<'tcx> for TypeVisitor<'tcx> {
    type ReturnType = Result<TyP<'tcx>, SyntaxError<'tcx>>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let builtin = match &self.source[node.byte_range()] {
            "bool" => Ty::Builtin(BuiltinType::Bool),
            "u8" => Ty::Builtin(BuiltinType::U8),
            "u16" => Ty::Builtin(BuiltinType::U16),
            "u32" => Ty::Builtin(BuiltinType::U32),
            "u64" => Ty::Builtin(BuiltinType::U64),
            "u128" => Ty::Builtin(BuiltinType::U128),
            "usize" => Ty::Builtin(BuiltinType::USize),
            "isize" => Ty::Builtin(BuiltinType::ISize),
            "i8" => Ty::Builtin(BuiltinType::I8),
            "i16" => Ty::Builtin(BuiltinType::I16),
            "i32" => Ty::Builtin(BuiltinType::I32),
            "i64" => Ty::Builtin(BuiltinType::I64),
            "i128" => Ty::Builtin(BuiltinType::I128),
            "f32" => Ty::Builtin(BuiltinType::F32),
            "f64" => Ty::Builtin(BuiltinType::F64),
            _ => unreachable!(),
        };

        Ok(self.global_ctx.intern(builtin))
    }

    fn visit_never_type(&mut self, _node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        Ok(self.global_ctx.intern(Ty::Builtin(BuiltinType::Never)))
    }

    fn visit_pointer_of(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(self.global_ctx.intern(Ty::Pointer(ty)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let len = self.source[node.child_by_field_name("size").unwrap().byte_range()]
            .parse()
            .unwrap();

        Ok(self.global_ctx.intern(Ty::Array(ty, len)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        Ok(self.global_ctx.intern(Ty::Slice(ty)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field_name("element", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        match &elements[..] {
            [] => Ok(self.global_ctx.intern(Ty::Builtin(BuiltinType::Void))),
            [ty] => Ok(*ty),
            _ => {
                let slice = self.global_ctx.arena.alloc_slice_copy(elements.as_slice());
                Ok(self.global_ctx.intern(Ty::Tuple(slice)))
            }
        }
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_function_pointer(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .child_by_field_name("parameters")
            .unwrap()
            .children_by_field_name("parameter", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        let type_node = if let Some(return_type_node) = node.child_by_field_name("return_type") {
            self.visit(return_type_node)?
        } else {
            self.global_ctx.intern(Ty::Builtin(BuiltinType::Void))
        };

        Ok(self.global_ctx.intern(Ty::Function(
            self.global_ctx.arena.alloc_slice_copy(elements.as_slice()),
            type_node,
        )))
    }
}

#[cfg(test)]
mod tests {
    use std::assert_matches::assert_matches;

    use crate::{
        common::{AluminaError, SyntaxError},
        name_resolution::scope::ScopeType,
        types::{BuiltinType, SymbolP, Ty, TyP},
        visitors::{pass1::FirstPassVisitor, types::TypeVisitor},
    };

    use super::*;

    trait AsTyP<'tcx> {
        fn as_typ(self, ctx: &'tcx GlobalCtx<'tcx>) -> TyP<'tcx>;
    }

    impl<'tcx> AsTyP<'tcx> for Ty<'tcx> {
        fn as_typ(self, ctx: &'tcx GlobalCtx<'tcx>) -> TyP<'tcx> {
            ctx.intern(self)
        }
    }

    fn parse<'tcx>(global_ctx: &'tcx GlobalCtx<'tcx>, src: &'tcx str) -> Scope<'tcx> {
        let parsed = global_ctx.arena.alloc(crate::parser::parse(src));
        let root_node = parsed.root_node();

        let root_scope = Scope::new();
        let module_scope = root_scope.make_child(ScopeType::Crate, "test");
        root_scope
            .add_item("test", Item::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(global_ctx, src, module_scope);
        visitor.visit(root_node).unwrap();

        root_scope
    }

    fn extract_type<'tcx>(
        global_ctx: &'tcx GlobalCtx<'tcx>,
        src: &'tcx str,
        root_scope: Scope<'tcx>,
    ) -> Result<TyP<'tcx>, SyntaxError<'tcx>> {
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

        let mut visitor = TypeVisitor::new(global_ctx, src, scope);
        visitor.visit(node)
    }

    #[test]
    fn test_typ_eq() {
        let ctx = GlobalCtx::new();

        let ty1 = Ty::Builtin(BuiltinType::I32);
        let ty2 = Ty::Builtin(BuiltinType::I32);

        let ptr1 = Ty::Pointer(ctx.intern(ty1));
        let ptr2 = Ty::Pointer(ctx.intern(ty2));

        let typ1 = ctx.intern(ptr1);
        let typ2 = ctx.intern(ptr2);

        assert_eq!(typ1, typ2);
    }

    fn test_parse_type<'tcx>(
        global_ctx: &'tcx GlobalCtx<'tcx>,
        typedef: &str,
        expected: TyP<'tcx>,
    ) {
        let src = global_ctx
            .arena
            .alloc_str(&format!("struct a {{ b: {}; }}", typedef));

        let root_scope = parse(&global_ctx, src);
        let result = extract_type(&global_ctx, src, root_scope).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_type_builtin() {
        let ctx = GlobalCtx::new();

        test_parse_type(&ctx, "i32", Ty::Builtin(BuiltinType::I32).as_typ(&ctx));
    }

    #[test]
    fn test_parse_type_array() {
        let ctx = GlobalCtx::new();

        test_parse_type(
            &ctx,
            "[u32; 16]",
            Ty::Array(Ty::Builtin(BuiltinType::U32).as_typ(&ctx), 16).as_typ(&ctx),
        );
    }

    #[test]
    fn test_parse_type_pointer() {
        let ctx = GlobalCtx::new();

        test_parse_type(
            &ctx,
            "&i32",
            Ty::Pointer(Ty::Builtin(BuiltinType::I32).as_typ(&ctx)).as_typ(&ctx),
        );
    }

    #[test]
    fn test_parse_function() {
        let ctx = GlobalCtx::new();

        test_parse_type(
            &ctx,
            "fn(u32) -> !",
            Ty::Function(
                &[Ty::Builtin(BuiltinType::U32).as_typ(&ctx)],
                Ty::Builtin(BuiltinType::Never).as_typ(&ctx),
            )
            .as_typ(&ctx),
        );
    }

    #[test]
    fn test_parse_type_tuple() {
        let ctx = GlobalCtx::new();

        test_parse_type(
            &ctx,
            "(i32, u32)",
            Ty::Tuple(&[
                Ty::Builtin(BuiltinType::I32).as_typ(&ctx),
                Ty::Builtin(BuiltinType::U32).as_typ(&ctx),
            ])
            .as_typ(&ctx),
        );
    }

    #[test]
    fn test_parse_type_empty_tuple() {
        let ctx = GlobalCtx::new();

        test_parse_type(&ctx, "()", Ty::Builtin(BuiltinType::Void).as_typ(&ctx));
    }

    #[test]
    fn test_parse_type_single_element_tuple() {
        let ctx = GlobalCtx::new();

        test_parse_type(&ctx, "(u32)", Ty::Builtin(BuiltinType::U32).as_typ(&ctx));
    }

    #[test]
    fn test_referenced_type() {
        let ctx = GlobalCtx::new();

        let src = r"
            mod foo {
                struct bar {}
            }

            struct a {
                b: foo::bar,
            }
            ";

        let root_scope = parse(&ctx, src);
        let result = extract_type(&ctx, src, root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_referenced_type_super() {
        let ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            mod goo {
                use super::bar;
            }
            struct bar {}
        }

        struct a {
            b: foo::goo::bar,
        }
        ";

        let root_scope = parse(&ctx, src);
        let result = extract_type(&ctx, src, root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_infinite_loop() {
        let ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            use super::bar::baz;
        }

        mod bar {
            use super::foo::baz;
        }

        struct a {
            b: foo::baz,
        }
        ";

        let root_scope = parse(&ctx, src);
        let err = extract_type(&ctx, src, root_scope).unwrap_err();

        assert_matches!(err.kind, AluminaError::CycleDetected);
    }

    #[test]
    fn test_referenced_type_crate() {
        let ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            struct bar {}
        }

        struct a {
            b: crate::foo::bar,
        }
        ";

        let root_scope = parse(&ctx, src);
        let result = extract_type(&ctx, src, root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_referenced_type_absolute() {
        let ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            struct bar {}
        }

        struct a {
            b: ::test::foo::bar,
        }
        ";

        let root_scope = parse(&ctx, src);
        let result = extract_type(&ctx, src, root_scope).unwrap();
        let symbol = ctx.get_symbol(0);

        assert_eq!(result, Ty::NamedType(symbol).as_typ(&ctx));
    }

    #[test]
    fn test_parse_complex_tuple() {
        let ctx = GlobalCtx::new();

        test_parse_type(
            &ctx,
            "(i32, [u32; 16], &i32)",
            Ty::Tuple(&[
                Ty::Builtin(BuiltinType::I32).as_typ(&ctx),
                Ty::Array(Ty::Builtin(BuiltinType::U32).as_typ(&ctx), 16).as_typ(&ctx),
                Ty::Pointer(Ty::Builtin(BuiltinType::I32).as_typ(&ctx)).as_typ(&ctx),
            ])
            .as_typ(&ctx),
        );
    }

    #[test]
    fn test_parse_type_never() {
        let ctx = GlobalCtx::new();

        test_parse_type(&ctx, "!", Ty::Builtin(BuiltinType::Never).as_typ(&ctx));
    }
}
