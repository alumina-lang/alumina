use crate::ast::AstCtx;
use crate::common::{ArenaAllocatable, CodeErrorKind};
use crate::name_resolution::resolver::ItemResolution;
use crate::parser::AluminaVisitor;
use crate::parser::ParseCtx;
use crate::{
    ast::{BuiltinType, Ty, TyP},
    common::{AluminaError, WithSpanDuringParsing},
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

    fn visit_typeref(&mut self, node: tree_sitter::Node<'src>) -> Result<TyP<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let res = match resolver
            .resolve_item(self.scope.clone(), path)
            .with_span(&self.scope, node)?
        {
            ItemResolution::Item(NamedItem::Type(ty, _, _)) => {
                self.ast.intern_type(Ty::NamedType(ty))
            }
            ItemResolution::Item(NamedItem::Placeholder(ty)) => {
                self.ast.intern_type(Ty::Placeholder(ty))
            }
            ItemResolution::Defered(_, _) => {
                return Err(CodeErrorKind::NoAssociatedTypes).with_span(&self.scope, node)
            }
            a => panic!("unreachable: {:?}", a),
        };

        Ok(res)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for TypeVisitor<'ast, 'src> {
    type ReturnType = Result<TyP<'ast>, AluminaError>;

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
        let is_mut = node.child_by_field_name("mut").is_some();

        Ok(self.ast.intern_type(Ty::Pointer(ty, !is_mut)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let is_mut = node.child_by_field_name("mut").is_some();

        Ok(self.ast.intern_type(Ty::Slice(ty, !is_mut)))
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
            _ => return Err(CodeErrorKind::UnexpectedGenericParams).with_span(&self.scope, node),
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
            .intern_type(Ty::Fn(elements.alloc_on(self.ast), type_node)))
    }
}
