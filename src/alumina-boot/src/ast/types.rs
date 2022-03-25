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
        scope::{NamedItemKind, Scope},
    },
    visitors::ScopedPathVisitor,
};

use super::{Bound, Span};

pub struct TypeVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    accept_protocol: bool,
    in_a_macro: bool,
}

impl<'ast, 'src> TypeVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>, in_a_macro: bool) -> Self {
        TypeVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            accept_protocol: false,
            in_a_macro,
        }
    }

    pub fn with_protocol(mut self) -> Self {
        self.accept_protocol = true;
        self
    }

    pub fn parse_protocol_bounds(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<&'ast [Bound<'ast>], AluminaError> {
        let mut bounds = Vec::new();
        let mut cursor = node.walk();

        for bound in node.children_by_field_name("bound", &mut cursor) {
            self.accept_protocol = true;
            bounds.push(Bound {
                span: Some(Span {
                    start: node.start_byte(),
                    end: node.end_byte(),
                    file: self.scope.code().unwrap().file_id(),
                }),
                negated: bound.child_by_field_name("negated").is_some(),
                typ: self.visit(bound.child_by_field_name("type").unwrap())?,
            });
        }

        Ok(bounds.alloc_on(self.ast))
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
                NamedItemKind::Protocol(ty, _, _) => {
                    if self.accept_protocol {
                        self.ast.intern_type(Ty::Protocol(ty))
                    } else {
                        return Err(CodeErrorKind::UnexpectedProtocol)
                            .with_span_from(&self.scope, node);
                    }
                }
                kind => {
                    return Err(CodeErrorKind::Unexpected(format!("{}", kind)))
                        .with_span_from(&self.scope, node)
                }
            },
            ItemResolution::Defered(_, _) => {
                return Err(CodeErrorKind::NoAssociatedTypes).with_span_from(&self.scope, node)
            }
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
        self.accept_protocol = false;
        Ok(self.ast.intern_type(Ty::Builtin(BuiltinType::Never)))
    }

    fn visit_pointer_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.accept_protocol = false;
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let is_mut = node.child_by_field_name("mut").is_some();

        Ok(self.ast.intern_type(Ty::Pointer(ty, !is_mut)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.accept_protocol = false;
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let is_mut = node.child_by_field_name("mut").is_some();

        Ok(self.ast.intern_type(Ty::Slice(ty, !is_mut)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.accept_protocol = false;
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let len = self
            .code
            .node_text(node.child_by_field_name("size").unwrap())
            .parse()
            .unwrap();

        Ok(self.ast.intern_type(Ty::Array(ty, len)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.accept_protocol = false;
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

    fn visit_generic_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let base = self.visit_typeref(node.child_by_field_name("type").unwrap())?;

        self.accept_protocol = false;
        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| self.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        let base = match *base {
            Ty::NamedType(ty) => ty,
            Ty::NamedFunction(ty) => ty,
            Ty::Protocol(ty) => ty,
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
        self.accept_protocol = false;

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
}
