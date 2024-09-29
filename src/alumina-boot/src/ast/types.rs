use crate::ast::expressions::ExpressionVisitor;
use crate::ast::{
    AstCtx, Bound, BuiltinType, Defered, ProtocolBounds, ProtocolBoundsKind, Span, Ty, TyP,
};
use crate::common::{AluminaError, ArenaAllocatable, CodeDiagnostic, WithSpanDuringParsing};
use crate::global_ctx::GlobalCtx;
use crate::parser::{AluminaVisitor, FieldKind, NodeExt, NodeKind, ParseCtx};
use crate::src::resolver::{ItemResolution, NameResolver};
use crate::src::scope::{NamedItemKind, Scope};
use crate::visitors::ScopedPathVisitor;

use super::MacroCtx;

pub struct TypeVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    macro_ctx: MacroCtx,
}

impl<'ast, 'src> TypeVisitor<'ast, 'src> {
    pub fn new(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        macro_ctx: MacroCtx,
    ) -> Self {
        TypeVisitor {
            global_ctx,
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            macro_ctx,
        }
    }

    pub fn parse_protocol_bounds(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<ProtocolBounds<'ast>, AluminaError> {
        let mut bounds = Vec::new();

        let (kind, node) = if node.child_by_field(FieldKind::AllBounds).is_some() {
            (ProtocolBoundsKind::All, node)
        } else if node.child_by_field(FieldKind::AnyBounds).is_some() {
            (ProtocolBoundsKind::Any, node)
        } else {
            // There are no bounds
            (ProtocolBoundsKind::All, node)
        };

        let mut cursor = node.walk();
        for bound in node.children_by_field(FieldKind::Bound, &mut cursor) {
            bounds.push(Bound {
                span: Some(Span::from_node(self.scope.file_id(), bound)),
                negated: bound.child_by_field(FieldKind::Negated).is_some(),
                ty: self.visit(bound.child_by_field(FieldKind::Type).unwrap())?,
            });
        }

        let bounds = bounds.alloc_on(self.ast);

        Ok(ProtocolBounds { bounds, kind })
    }

    fn visit_typeref(&mut self, node: tree_sitter::Node<'src>) -> Result<TyP<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.macro_ctx);
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let res = match resolver
            .resolve_item(self.scope.clone(), path)
            .with_span_from(&self.scope, node)?
        {
            ItemResolution::Item(item) => match item.kind {
                NamedItemKind::Type(ty) => self.ast.intern_type(Ty::Item(ty)),
                NamedItemKind::TypeDef(ty) => self.ast.intern_type(Ty::Item(ty)),
                NamedItemKind::Function(ty) => self.ast.intern_type(Ty::Item(ty)),
                NamedItemKind::Protocol(ty) => self.ast.intern_type(Ty::Item(ty)),
                NamedItemKind::Const(ty) => self.ast.intern_type(Ty::Item(ty)),
                NamedItemKind::Static(ty) => self.ast.intern_type(Ty::Item(ty)),
                NamedItemKind::Placeholder(ty) => self.ast.intern_type(Ty::Placeholder(ty)),
                kind => {
                    return Err(CodeDiagnostic::Unexpected(format!("{}", kind)))
                        .with_span_from(&self.scope, node)
                }
            },
            ItemResolution::Defered(ty, name) => self.ast.intern_type(Ty::Defered(Defered {
                ty: self.ast.intern_type(ty),
                name: name.0,
            })),
        };

        Ok(res)
    }

    #[allow(non_snake_case)]
    fn visit_fn_or_Fn(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<(&'ast [TyP<'ast>], TyP<'ast>), AluminaError> {
        let mut cursor = node.walk();
        let elements = node
            .child_by_field(FieldKind::Parameters)
            .unwrap()
            .children_by_field(FieldKind::Parameter, &mut cursor)
            .map(|child| {
                if child.kind_typed() == NodeKind::EtCeteraOf {
                    self.visit(child.child_by_field(FieldKind::Inner).unwrap())
                        .map(|ty| self.ast.intern_type(Ty::EtCetera(ty)))
                } else {
                    self.visit(child)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        let type_node = if let Some(return_type_node) = node.child_by_field(FieldKind::ReturnType) {
            self.visit(return_type_node)?
        } else {
            self.ast.intern_type(Ty::void())
        };

        Ok((elements.alloc_on(self.ast), type_node))
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for TypeVisitor<'ast, 'src> {
    type ReturnType = Result<TyP<'ast>, AluminaError>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let builtin = match self.code.node_text(node) {
            "void" => Ty::void(),
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
        let ty = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;
        let is_mut = node.child_by_field(FieldKind::Mut).is_some();

        Ok(self.ast.intern_type(Ty::Pointer(ty, !is_mut)))
    }

    fn visit_deref_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;

        Ok(self.ast.intern_type(Ty::Deref(ty)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;
        let is_mut = node.child_by_field(FieldKind::Mut).is_some();

        Ok(self.ast.intern_type(Ty::Slice(ty, !is_mut)))
    }

    fn visit_dyn_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let is_mut = node.child_by_field(FieldKind::Mut).is_some();

        let mut cursor = node.walk();
        let inner = node
            .children_by_field(FieldKind::Inner, &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(self
            .ast
            .intern_type(Ty::Dyn(inner.alloc_on(self.ast), !is_mut)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;
        let mut visitor = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.clone(),
            self.macro_ctx,
        );
        let size = visitor.visit(node.child_by_field(FieldKind::Size).unwrap())?;

        Ok(self.ast.intern_type(Ty::Array(ty, size)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field(FieldKind::Element, &mut cursor)
            .map(|child| {
                if child.kind_typed() == NodeKind::EtCeteraOf {
                    self.visit(child.child_by_field(FieldKind::Inner).unwrap())
                        .map(|ty| self.ast.intern_type(Ty::EtCetera(ty)))
                } else {
                    self.visit(child)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        let slice = elements.alloc_on(self.ast);
        Ok(self.ast.intern_type(Ty::Tuple(slice)))
    }

    fn visit_et_cetera_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Err(CodeDiagnostic::EtCeteraInUnsupported).with_span_from(&self.scope, node)
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_tuple_index_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;
        let mut visitor = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.clone(),
            self.macro_ctx,
        );
        let index = visitor.visit(node.child_by_field(FieldKind::Index).unwrap())?;

        Ok(self.ast.intern_type(Ty::TupleIndex(inner, index)))
    }

    fn visit_type_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut visitor = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.clone(),
            self.macro_ctx,
        );
        let expr = visitor.visit(node.child_by_field(FieldKind::Inner).unwrap())?;

        Ok(self.ast.intern_type(Ty::TypeOf(expr)))
    }

    fn visit_generic_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let base = self.visit_typeref(node.child_by_field(FieldKind::Type).unwrap())?;

        let arguments_node = node.child_by_field(FieldKind::TypeArguments).unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field(FieldKind::Type, &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        match *base {
            Ty::Item(_) | Ty::Defered(_) => {}
            _ => {
                return Err(CodeDiagnostic::UnexpectedGenericParams)
                    .with_span_from(&self.scope, node)
            }
        };

        Ok(self
            .ast
            .intern_type(Ty::Generic(base, arguments.alloc_on(self.ast))))
    }

    fn visit_generic_type_with_turbofish(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        self.visit_generic_type(node)
    }

    fn visit_function_pointer(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (args, ret) = self.visit_fn_or_Fn(node)?;

        Ok(self.ast.intern_type(Ty::FunctionPointer(args, ret)))
    }

    fn visit_function_protocol(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (args, ret) = self.visit_fn_or_Fn(node)?;

        Ok(self.ast.intern_type(Ty::FunctionProtocol(args, ret)))
    }

    fn visit_when_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut visitor = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.clone(),
            self.macro_ctx,
        );
        let cond = visitor.visit(node.child_by_field(FieldKind::Condition).unwrap())?;
        let then = self.visit(node.child_by_field(FieldKind::Consequence).unwrap())?;
        let els = self.visit(node.child_by_field(FieldKind::Alternative).unwrap())?;

        Ok(self.ast.intern_type(Ty::When(cond, then, els)))
    }
}
