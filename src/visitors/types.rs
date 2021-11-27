use crate::AluminaVisitor;
use crate::{
    common::SyntaxError,
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

        let res = match resolver.resolve_type_item(self.scope.clone(), &path) {
            Some(Item::Type(ty, _, _)) => Ok(self.global_ctx.intern(Ty::StructOrEnum(ty))),
            Some(Item::Placeholder(ty)) => Ok(self.global_ctx.intern(Ty::Placeholder(ty))),
            None => Err(SyntaxError("unresolved type", node)),
            _ => unreachable!(),
        };
        res
    }
}

impl<'tcx> AluminaVisitor<'tcx> for TypeVisitor<'tcx> {
    type ReturnType = Result<TyP<'tcx>, SyntaxError<'tcx>>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let builtin = match &self.source[node.byte_range()] {
            "void" => Ty::Builtin(BuiltinType::Void),
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
            _ => return Err(SyntaxError("unknown type", node)),
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

        let slice = self.global_ctx.arena.alloc_slice_copy(elements.as_slice());

        Ok(self.global_ctx.intern(Ty::Tuple(slice)))
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        self.visit_typeref(node)
    }
}
