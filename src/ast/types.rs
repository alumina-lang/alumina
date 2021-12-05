use crate::ast::AstCtx;
use crate::common::{AluminaError, ArenaAllocatable};
use crate::name_resolution::resolver::ItemResolution;
use crate::parser::ParseCtx;
use crate::AluminaVisitor;
use crate::{
    ast::{BuiltinType, Ty, TyP},
    common::{SyntaxError, ToSyntaxError},
    name_resolution::{
        resolver::NameResolver,
        scope::{NamedItem, Scope},
    },
    visitors::ScopedPathVisitor,
};

pub struct TypeVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
}

impl<'ast, 'src> TypeVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        TypeVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
        }
    }

    fn visit_typeref(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<TyP<'ast>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let res = match resolver
            .resolve_item(self.scope.clone(), path)
            .to_syntax_error(node)?
        {
            ItemResolution::Item(NamedItem::Type(ty, _, _)) => {
                self.ast.intern_type(Ty::NamedType(ty))
            }
            ItemResolution::Item(NamedItem::Placeholder(ty)) => {
                self.ast.intern_type(Ty::Placeholder(ty))
            }
            ItemResolution::Defered(_, _) => {
                return Err(AluminaError::NoAssociatedTypes).to_syntax_error(node)
            }
            a => panic!("unreachable: {:?}", a),
        };

        Ok(res)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for TypeVisitor<'ast, 'src> {
    type ReturnType = Result<TyP<'ast>, SyntaxError<'src>>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let builtin = match self.code.node_text(node) {
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

        Ok(self.ast.intern_type(builtin))
    }

    fn visit_never_type(&mut self, _node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self.ast.intern_type(Ty::Builtin(BuiltinType::Never)))
    }

    fn visit_pointer_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(self.ast.intern_type(Ty::Pointer(ty)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let len = self
            .code
            .node_text(node.child_by_field_name("size").unwrap())
            .parse()
            .unwrap();

        Ok(self.ast.intern_type(Ty::Array(ty, len)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        Ok(self.ast.intern_type(Ty::Slice(ty)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field_name("element", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        match &elements[..] {
            [] => Ok(self.ast.intern_type(Ty::Builtin(BuiltinType::Void))),
            [ty] => Ok(*ty),
            _ => {
                let slice = elements.alloc_on(self.ast);
                Ok(self.ast.intern_type(Ty::Tuple(slice)))
            }
        }
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_generic_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let base = self.visit_typeref(node.child_by_field_name("type").unwrap())?;
        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        let base = match *base {
            Ty::NamedType(ty) => ty,
            _ => return Err(AluminaError::UnexpectedGenericParams).to_syntax_error(node),
        };

        Ok(self
            .ast
            .intern_type(Ty::GenericType(base, arguments.alloc_on(self.ast))))
    }

    fn visit_generic_type_with_turbofish(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        self.visit_generic_type(node)
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
            self.ast.intern_type(Ty::Builtin(BuiltinType::Void))
        };

        Ok(self
            .ast
            .intern_type(Ty::Function(elements.alloc_on(self.ast), type_node)))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::AstCtx,
        ast::{BuiltinType, Ty, TyP},
        common::SyntaxError,
        name_resolution::scope::{NamedItem, Scope, ScopeType},
        parser::AluminaVisitor,
        parser::ParseCtx,
        visitors::pass1::FirstPassVisitor,
    };

    use super::TypeVisitor;

    fn first_pass<'ast, 'src>(
        ast: &'ast AstCtx<'ast>,
        code: &'src ParseCtx<'src>,
    ) -> Result<Scope<'ast, 'src>, SyntaxError<'src>> {
        let root_scope = Scope::new_root();

        let module_scope =
            root_scope.named_child_with_ctx(ScopeType::Crate, "test", code.to_owned());

        root_scope
            .add_item("test", NamedItem::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(ast, module_scope);
        visitor.visit(code.root_node())?;

        Ok(root_scope)
    }

    fn extract_type<'ast, 'src>(
        ast: &'ast AstCtx<'ast>,
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

        let mut visitor = TypeVisitor::new(ast, scope);
        visitor.visit(node)
    }

    #[test]
    fn test_typ_eq() {
        let ctx = AstCtx::new();

        let ty1 = Ty::Builtin(BuiltinType::I32);
        let ty2 = Ty::Builtin(BuiltinType::I32);

        let ptr1 = Ty::Pointer(ctx.intern_type(ty1));
        let ptr2 = Ty::Pointer(ctx.intern_type(ty2));

        let typ1 = ctx.intern_type(ptr1);
        let typ2 = ctx.intern_type(ptr2);

        assert_eq!(typ1, typ2);
    }

    fn test_parse_type<'ast>(ast: &'ast AstCtx<'ast>, typedef: &str, expected: TyP<'ast>) {
        let src = ast
            .arena
            .alloc_str(&format!("struct a {{ b: {}; }}", typedef));

        let code = ParseCtx::from_source(src);
        let root_scope = first_pass(ast, &code).unwrap();
        let result = extract_type(ast, root_scope).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_type_builtin() {
        let ctx = AstCtx::new();

        test_parse_type(&ctx, "i32", &Ty::Builtin(BuiltinType::I32));
    }

    #[test]
    fn test_parse_type_array() {
        let ctx = AstCtx::new();

        test_parse_type(
            &ctx,
            "[u32; 16]",
            &Ty::Array(&Ty::Builtin(BuiltinType::U32), 16),
        );
    }

    #[test]
    fn test_parse_type_pointer() {
        let ctx = AstCtx::new();

        test_parse_type(&ctx, "&i32", &Ty::Pointer(&Ty::Builtin(BuiltinType::I32)));
    }

    #[test]
    fn test_parse_function() {
        let ctx = AstCtx::new();

        test_parse_type(
            &ctx,
            "fn(u32) -> !",
            &Ty::Function(
                &[&Ty::Builtin(BuiltinType::U32)],
                &Ty::Builtin(BuiltinType::Never),
            ),
        );
    }

    #[test]
    fn test_parse_hof() {
        let ctx = AstCtx::new();

        test_parse_type(
            &ctx,
            "fn(u32) -> fn(u32) -> u32",
            &Ty::Function(
                &[&Ty::Builtin(BuiltinType::U32)],
                &Ty::Function(
                    &[&Ty::Builtin(BuiltinType::U32)],
                    &Ty::Builtin(BuiltinType::U32),
                ),
            ),
        );
    }

    #[test]
    fn test_parse_type_tuple() {
        let ctx = AstCtx::new();

        test_parse_type(
            &ctx,
            "(i32, u32)",
            &Ty::Tuple(&[
                &Ty::Builtin(BuiltinType::I32),
                &Ty::Builtin(BuiltinType::U32),
            ]),
        );
    }

    #[test]
    fn test_parse_type_empty_tuple() {
        let ctx = AstCtx::new();

        test_parse_type(&ctx, "()", &Ty::Builtin(BuiltinType::Void));
    }

    #[test]
    fn test_parse_type_single_element_tuple() {
        let ctx = AstCtx::new();

        test_parse_type(&ctx, "(u32)", &Ty::Builtin(BuiltinType::U32));
    }

    #[test]
    fn test_parse_complex_tuple() {
        let ctx = AstCtx::new();

        test_parse_type(
            &ctx,
            "(i32, [u32; 16], &i32)",
            &Ty::Tuple(&[
                &Ty::Builtin(BuiltinType::I32),
                &Ty::Array(&Ty::Builtin(BuiltinType::U32), 16),
                &Ty::Pointer(&Ty::Builtin(BuiltinType::I32)),
            ]),
        );
    }

    #[test]
    fn test_parse_type_never() {
        let ctx = AstCtx::new();

        test_parse_type(&ctx, "!", &Ty::Builtin(BuiltinType::Never));
    }
}
