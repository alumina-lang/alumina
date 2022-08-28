use crate::ast::AstCtx;
use crate::common::{ArenaAllocatable, CodeErrorKind};
use crate::global_ctx::GlobalCtx;
use crate::name_resolution::resolver::ItemResolution;
use crate::parser::AluminaVisitor;
use crate::parser::ParseCtx;
use crate::{
    ast::{BuiltinType, Ty, TyP},
    common::{AluminaError, WithSpanDuringParsing},
    name_resolution::{
        resolver::NameResolver,
        scope::{NamedItemKind, Scope},
    },
    visitors::ScopedPathVisitor,
};

use super::expressions::ExpressionVisitor;
use super::{Bound, Defered, ProtocolBounds, ProtocolBoundsKind, Span, StaticIfCondition};

pub struct TypeVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    in_a_macro: bool,
}

impl<'ast, 'src> TypeVisitor<'ast, 'src> {
    pub fn new(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        in_a_macro: bool,
    ) -> Self {
        TypeVisitor {
            global_ctx,
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            in_a_macro,
        }
    }

    pub fn parse_protocol_bounds(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<ProtocolBounds<'ast>, AluminaError> {
        let mut bounds = Vec::new();

        let (kind, node) = if node.child_by_field_name("all_bounds").is_some() {
            (ProtocolBoundsKind::All, node)
        } else if node.child_by_field_name("any_bounds").is_some() {
            (ProtocolBoundsKind::Any, node)
        } else {
            // There are no bounds
            (ProtocolBoundsKind::All, node)
        };

        let mut cursor = node.walk();
        for bound in node.children_by_field_name("bound", &mut cursor) {
            bounds.push(Bound {
                span: Some(Span {
                    start: bound.start_byte(),
                    end: bound.end_byte(),
                    line: bound.start_position().row,
                    column: bound.start_position().column,
                    file: self.scope.code().unwrap().file_id(),
                }),
                negated: bound.child_by_field_name("negated").is_some(),
                typ: self.visit(bound.child_by_field_name("type").unwrap())?,
            });
        }

        let bounds = bounds.alloc_on(self.ast);

        Ok(ProtocolBounds { bounds, kind })
    }

    fn visit_typeref(&mut self, node: tree_sitter::Node<'src>) -> Result<TyP<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let res = match resolver
            .resolve_item(self.scope.clone(), path)
            .with_span_from(&self.scope, node)?
        {
            ItemResolution::Item(item) => match item.kind {
                NamedItemKind::Type(ty, _, _) => self.ast.intern_type(Ty::NamedType(ty)),
                NamedItemKind::TypeDef(ty, _, _) => self.ast.intern_type(Ty::NamedType(ty)),
                NamedItemKind::Placeholder(ty, _) => self.ast.intern_type(Ty::Placeholder(ty)),
                NamedItemKind::Function(ty, _, _) => self.ast.intern_type(Ty::NamedFunction(ty)),
                NamedItemKind::Protocol(ty, _, _) => self.ast.intern_type(Ty::Protocol(ty)),
                kind => {
                    return Err(CodeErrorKind::Unexpected(format!("{}", kind)))
                        .with_span_from(&self.scope, node)
                }
            },
            ItemResolution::Defered(typ, name) => self.ast.intern_type(Ty::Defered(Defered {
                typ: self.ast.intern_type(typ),
                name: name.0,
            })),
        };

        Ok(res)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for TypeVisitor<'ast, 'src> {
    type ReturnType = Result<TyP<'ast>, AluminaError>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let builtin = match self.code.node_text(node) {
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

    fn visit_dyn_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let is_mut = node.child_by_field_name("mut").is_some();

        let mut cursor = node.walk();
        let inner = node
            .children_by_field_name("inner", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(self
            .ast
            .intern_type(Ty::Dyn(inner.alloc_on(self.ast), !is_mut)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let mut visitor = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.clone(),
            self.in_a_macro,
        );
        let size = visitor.visit(node.child_by_field_name("size").unwrap())?;

        Ok(self.ast.intern_type(Ty::Array(ty, size)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field_name("element", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        match &elements[..] {
            [] => Ok(self.ast.intern_type(Ty::Builtin(BuiltinType::Void))),
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

    fn visit_type_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut visitor = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.clone(),
            self.in_a_macro,
        );
        let expr = visitor.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(self.ast.intern_type(Ty::TypeOf(expr)))
    }

    fn visit_generic_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let base = self.visit_typeref(node.child_by_field_name("type").unwrap())?;

        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        match *base {
            Ty::NamedType(_) | Ty::NamedFunction(_) | Ty::Protocol(_) | Ty::Defered(_) => {}
            _ => {
                return Err(CodeErrorKind::UnexpectedGenericParams)
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
            .intern_type(Ty::FunctionPointer(elements.alloc_on(self.ast), type_node)))
    }

    fn visit_when_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let typecheck_node = node.child_by_field_name("type_check").unwrap();
        let typ = self.visit(typecheck_node.child_by_field_name("lhs").unwrap())?;
        let bounds = self.parse_protocol_bounds(typecheck_node)?;
        let cond = StaticIfCondition { typ, bounds };

        let then = self.visit(node.child_by_field_name("consequence").unwrap())?;
        let els = self.visit(node.child_by_field_name("alternative").unwrap())?;

        Ok(self.ast.intern_type(Ty::When(cond, then, els)))
    }
}
