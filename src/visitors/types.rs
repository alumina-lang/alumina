use crate::parser::ParseCtx;
use crate::AluminaVisitor;
use crate::{
    ast::{BuiltinType, Ty, TyP},
    common::{SyntaxError, ToSyntaxError},
    name_resolution::{
        resolver::NameResolver,
        scope::{Item, Scope},
    },
    visitors::ScopedPathVisitor,
};

pub struct TypeVisitor<'gcx, 'src> {
    parse_ctx: ParseCtx<'gcx, 'src>,
    scope: Scope<'gcx, 'src>,
}

impl<'gcx, 'src> TypeVisitor<'gcx, 'src> {
    pub fn new(scope: Scope<'gcx, 'src>) -> Self {
        TypeVisitor {
            parse_ctx: scope
                .parse_ctx()
                .expect("cannot run on scope without parse context"),
            scope,
        }
    }

    fn visit_typeref(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<TyP<'gcx>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let res = match resolver
            .resolve_type_item(self.scope.clone(), path)
            .to_syntax_error(node)?
        {
            Item::Type(ty, _, _) => self.parse_ctx.intern_type(Ty::NamedType(ty)),
            Item::Placeholder(ty) => self.parse_ctx.intern_type(Ty::Placeholder(ty)),
            _ => unreachable!(),
        };

        Ok(res)
    }
}

impl<'gcx, 'src> AluminaVisitor<'src> for TypeVisitor<'gcx, 'src> {
    type ReturnType = Result<TyP<'gcx>, SyntaxError<'src>>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let builtin = match self.parse_ctx.node_text(node) {
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

        Ok(self.parse_ctx.intern_type(builtin))
    }

    fn visit_never_type(&mut self, _node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self.parse_ctx.intern_type(Ty::Builtin(BuiltinType::Never)))
    }

    fn visit_pointer_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(self.parse_ctx.intern_type(Ty::Pointer(ty)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let len = self
            .parse_ctx
            .node_text(node.child_by_field_name("size").unwrap())
            .parse()
            .unwrap();

        Ok(self.parse_ctx.intern_type(Ty::Array(ty, len)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        Ok(self.parse_ctx.intern_type(Ty::Slice(ty)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field_name("element", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        match &elements[..] {
            [] => Ok(self.parse_ctx.intern_type(Ty::Builtin(BuiltinType::Void))),
            [ty] => Ok(*ty),
            _ => {
                let slice = self.parse_ctx.alloc_slice(elements.as_slice());
                Ok(self.parse_ctx.intern_type(Ty::Tuple(slice)))
            }
        }
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_function_pointer(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
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
            self.parse_ctx.intern_type(Ty::Builtin(BuiltinType::Void))
        };

        Ok(self.parse_ctx.intern_type(Ty::Function(
            self.parse_ctx.alloc_slice(elements.as_slice()),
            type_node,
        )))
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        ast::{BuiltinType, Ty, TyP},
        common::SyntaxError,
        context::GlobalCtx,
        name_resolution::scope::{Item, Scope, ScopeType},
        parser::AluminaVisitor,
        parser::ParseCtx,
        visitors::{pass1::FirstPassVisitor, types::TypeVisitor},
    };

    trait AsTyP<'gcx> {
        fn as_typ(self, ctx: &'gcx GlobalCtx<'gcx>) -> TyP<'gcx>;
    }

    impl<'gcx> AsTyP<'gcx> for Ty<'gcx> {
        fn as_typ(self, ctx: &'gcx GlobalCtx<'gcx>) -> TyP<'gcx> {
            ctx.intern_type(self)
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
    fn test_typ_eq() {
        let ctx = GlobalCtx::new();

        let ty1 = Ty::Builtin(BuiltinType::I32);
        let ty2 = Ty::Builtin(BuiltinType::I32);

        let ptr1 = Ty::Pointer(ctx.intern_type(ty1));
        let ptr2 = Ty::Pointer(ctx.intern_type(ty2));

        let typ1 = ctx.intern_type(ptr1);
        let typ2 = ctx.intern_type(ptr2);

        assert_eq!(typ1, typ2);
    }

    fn test_parse_type<'gcx>(
        global_ctx: &'gcx GlobalCtx<'gcx>,
        typedef: &str,
        expected: TyP<'gcx>,
    ) {
        let src = global_ctx
            .arena
            .alloc_str(&format!("struct a {{ b: {}; }}", typedef));

        let parse_ctx = ParseCtx::from_source(global_ctx, src);
        let root_scope = first_pass(&parse_ctx).unwrap();
        let result = extract_type(root_scope).unwrap();

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
    fn test_parse_hof() {
        let ctx = GlobalCtx::new();

        test_parse_type(
            &ctx,
            "fn(u32) -> fn(u32) -> u32",
            Ty::Function(
                &[Ty::Builtin(BuiltinType::U32).as_typ(&ctx)],
                Ty::Function(
                    &[Ty::Builtin(BuiltinType::U32).as_typ(&ctx)],
                    Ty::Builtin(BuiltinType::U32).as_typ(&ctx),
                )
                .as_typ(&ctx),
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
