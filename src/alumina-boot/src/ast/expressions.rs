use std::collections::{HashMap, HashSet};

use crate::ast::{AstCtx, FieldInitializer};
use crate::ast::{BinOp, Expr, ExprP, LetDeclaration, Lit, Statement, UnOp};
use crate::common::ArenaAllocatable;
use crate::common::CodeErrorKind;

use crate::global_ctx::GlobalCtx;
use crate::name_resolution::pass1::FirstPassVisitor;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::resolver::ItemResolution;
use crate::name_resolution::scope::{BoundItemType, NamedItem, ScopeType};
use crate::parser::AluminaVisitor;
use crate::parser::ParseCtx;

use crate::visitors::UseClauseVisitor;
use crate::visitors::{AttributeVisitor, ScopedPathVisitor};
use crate::{
    common::{AluminaError, WithSpanDuringParsing},
    name_resolution::{
        resolver::NameResolver,
        scope::{NamedItemKind, Scope},
    },
};

use super::macros::{MacroExpander, MacroMaker};
use super::maker::AstItemMaker;
use super::types::TypeVisitor;
use super::{
    AstId, BuiltinType, ClosureBinding, Defered, ExprKind, FnKind, Function, Item, ItemP,
    Parameter, Placeholder, Span, StatementKind, StaticIfCondition, Ty, TyP,
};

macro_rules! with_block_scope {
    ($self:ident, $body:expr) => {{
        let child_scope = $self.scope.anonymous_child(ScopeType::Block);
        let previous_scope = std::mem::replace(&mut $self.scope, child_scope);
        let result = $body;
        $self.scope = previous_scope;
        result
    }};
}

trait Spannable<'ast, 'src>
where
    Self: Sized,
{
    type ReturnType;
    fn alloc_with_span(self, ast: &'ast AstCtx<'ast>, span: Span) -> Self::ReturnType;

    fn alloc_with_span_from(
        self,
        ast: &'ast AstCtx<'ast>,
        scope: &Scope<'ast, 'src>,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        self.alloc_with_span(ast, span)
    }

    fn alloc_with_no_span(self, ast: &'ast AstCtx<'ast>) -> Self::ReturnType;
}

impl<'ast, 'src> Spannable<'ast, 'src> for ExprKind<'ast> {
    type ReturnType = ExprP<'ast>;

    fn alloc_with_span(self, ast: &'ast AstCtx<'ast>, span: Span) -> ExprP<'ast> {
        Expr {
            kind: self,
            span: Some(span),
        }
        .alloc_on(ast)
    }

    fn alloc_with_no_span(self, ast: &'ast AstCtx<'ast>) -> ExprP<'ast> {
        Expr {
            kind: self,
            span: None,
        }
        .alloc_on(ast)
    }
}

impl<'ast, 'src> Spannable<'ast, 'src> for StatementKind<'ast> {
    type ReturnType = Statement<'ast>;

    fn alloc_with_span(self, _ast: &'ast AstCtx<'ast>, span: Span) -> Statement<'ast> {
        Statement {
            kind: self,
            span: Some(span),
        }
    }

    fn alloc_with_no_span(self, _ast: &'ast AstCtx<'ast>) -> Statement<'ast> {
        Statement {
            kind: self,
            span: None,
        }
    }
}

pub struct ExpressionVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    global_ctx: GlobalCtx,
    scope: Scope<'ast, 'src>,
    in_a_loop: bool,
    in_a_macro: bool,
    has_et_cetera: bool,
}
macro_rules! suffixed_literals {
    ($e:expr, $($suffix:literal => $typ:path),+) => {
        match $e {
            $(
                v if v.ends_with($suffix) => (&v[..v.len() - $suffix.len()], Some($typ)),
            )+
            v => (v, None)
        }
    };
    ($e:expr, $($suffix:literal => $typ:path,)+) => {
        suffixed_literals!($e, $($suffix => $typ),+)
    };
}

impl<'ast, 'src> ExpressionVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        global_ctx: GlobalCtx,
        scope: Scope<'ast, 'src>,
        in_a_macro: bool,
    ) -> Self {
        ExpressionVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            global_ctx,
            in_a_macro,
            in_a_loop: false,
            has_et_cetera: false,
        }
    }

    pub fn new_for_macro(
        ast: &'ast AstCtx<'ast>,
        global_ctx: GlobalCtx,
        scope: Scope<'ast, 'src>,
        has_et_cetera: bool,
    ) -> Self {
        ExpressionVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            global_ctx,
            in_a_loop: false,
            in_a_macro: true,
            has_et_cetera,
        }
    }

    pub fn generate(mut self, node: tree_sitter::Node<'src>) -> Result<ExprP<'ast>, AluminaError> {
        let result = self.visit(node)?;
        Ok(result)
    }

    fn visit_ref(&mut self, node: tree_sitter::Node<'src>) -> Result<ExprP<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let expr = match resolver
            .resolve_item(self.scope.clone(), path.clone())
            .with_span_from(&self.scope, node)?
        {
            ItemResolution::Item(item) => match item.kind {
                NamedItemKind::Function(fun, _, _) => ExprKind::Fn(FnKind::Normal(fun), None),
                NamedItemKind::Method(fun, _, _) => ExprKind::Fn(FnKind::Normal(fun), None),
                NamedItemKind::Local(var) => ExprKind::Local(var),
                NamedItemKind::BoundValue(self_id, var, bound_type) => {
                    ExprKind::BoundParam(self_id, var, bound_type)
                }
                NamedItemKind::MacroParameter(var, _) => ExprKind::Local(var),
                NamedItemKind::Parameter(var, _) => ExprKind::Local(var),
                NamedItemKind::Static(var, _) => ExprKind::Static(var),
                NamedItemKind::Const(var, _) => ExprKind::Const(var),
                NamedItemKind::EnumMember(typ, var, _) => ExprKind::EnumValue(typ, var),
                NamedItemKind::Macro(_, _, _) => {
                    return Err(CodeErrorKind::IsAMacro(path.to_string()))
                        .with_span_from(&self.scope, node)
                }
                kind => {
                    return Err(CodeErrorKind::Unexpected(format!("{}", kind)))
                        .with_span_from(&self.scope, node)
                }
            },
            ItemResolution::Defered(ty, name) => {
                let name = name.0.alloc_on(self.ast);
                let typ = self.ast.intern_type(ty);
                ExprKind::Defered(Defered { typ, name })
            }
        };

        Ok(expr.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_statement(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<Vec<Statement<'ast>>, AluminaError> {
        let inner = node.child_by_field_name("inner").unwrap();
        let attributes = match AttributeVisitor::parse_attributes(
            self.global_ctx.clone(),
            self.ast,
            self.scope.clone(),
            inner,
            None,
        )? {
            Some(attributes) => attributes,
            None => return Ok(vec![]),
        };

        let result = match inner.kind() {
            "empty_statement" => vec![],
            "let_declaration" => {
                let typ = inner
                    .child_by_field_name("type")
                    .map(|n| {
                        TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro).visit(n)
                    })
                    .transpose()?;

                let value_id = self.ast.make_id();
                let value = inner
                    .child_by_field_name("value")
                    .map(|n| self.visit(n))
                    .transpose()?;

                let let_decl = LetDeclaration {
                    id: value_id,
                    typ,
                    value,
                };

                let mut statements = Vec::new();
                if let Some(name) = inner.child_by_field_name("name") {
                    let name = self.code.node_text(name).alloc_on(self.ast);

                    self.scope
                        .add_item(
                            Some(name),
                            NamedItem::new_default(NamedItemKind::Local(value_id)),
                        )
                        .with_span_from(&self.scope, inner)?;

                    statements.push(
                        StatementKind::LetDeclaration(let_decl).alloc_with_span_from(
                            self.ast,
                            &self.scope,
                            node,
                        ),
                    );
                } else {
                    // Tuple unpacking
                    let mut cursor = inner.walk();
                    for (idx, elem) in inner
                        .children_by_field_name("element", &mut cursor)
                        .enumerate()
                    {
                        let name = self.code.node_text(elem).alloc_on(self.ast);
                        let elem_id = self.ast.make_id();

                        let rhs = ExprKind::TupleIndex(
                            ExprKind::Local(value_id).alloc_with_span_from(
                                self.ast,
                                &self.scope,
                                elem,
                            ),
                            idx,
                        )
                        .alloc_with_span_from(self.ast, &self.scope, elem);

                        let elem_decl = LetDeclaration {
                            id: elem_id,
                            typ: None,
                            value: Some(rhs),
                        };

                        statements.push(
                            StatementKind::LetDeclaration(elem_decl).alloc_with_span_from(
                                self.ast,
                                &self.scope,
                                node,
                            ),
                        );

                        self.scope
                            .add_item(
                                Some(name),
                                NamedItem::new_default(NamedItemKind::Local(elem_id)),
                            )
                            .with_span_from(&self.scope, elem)?;
                    }

                    statements.insert(
                        0,
                        StatementKind::LetDeclaration(let_decl).alloc_with_span_from(
                            self.ast,
                            &self.scope,
                            node,
                        ),
                    );
                }
                statements
            }
            "use_declaration" => {
                UseClauseVisitor::new(self.ast, self.scope.clone(), attributes, self.in_a_macro)
                    .visit(inner.child_by_field_name("argument").unwrap())?;
                vec![]
            }
            "expression_statement" => vec![StatementKind::Expression(
                self.visit(inner.child_by_field_name("inner").unwrap())?,
            )
            .alloc_with_span_from(self.ast, &self.scope, node)],
            "macro_definition" => {
                FirstPassVisitor::new(self.global_ctx.clone(), self.ast, self.scope.clone())
                    .visit_macro_definition(inner)?;
                vec![]
            }
            "const_declaration" => {
                let name = self
                    .code
                    .node_text(inner.child_by_field_name("name").unwrap())
                    .alloc_on(self.ast);
                let item = NamedItem::new(
                    NamedItemKind::Const(self.ast.make_symbol(), inner),
                    attributes,
                );
                self.scope
                    .add_item(Some(name), item.clone())
                    .with_span_from(&self.scope, inner)?;
                AstItemMaker::new(self.ast, self.global_ctx.clone(), self.in_a_macro).make_item(
                    self.scope.clone(),
                    Some(name),
                    item,
                )?;
                vec![]
            }
            _ => unimplemented!(),
        };

        Ok(result)
    }

    fn extract_expression_ending_with_block(
        &self,
        last_node: Option<tree_sitter::Node<'src>>,
        statements: &mut Vec<Statement<'ast>>,
    ) -> ExprP<'ast> {
        let last_node = match last_node {
            Some(n) => n,
            None => return ExprKind::Void.alloc_with_no_span(self.ast),
        };

        let expression_node = match last_node.kind() {
            "expression_statement" => last_node.child_by_field_name("inner").unwrap(),
            _ => return ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, last_node),
        };

        match expression_node.kind() {
            "block" | "if_expression" | "switch_expression" | "while_expression"
            | "loop_expression" | "for_expression" => match statements.pop() {
                Some(Statement {
                    kind: StatementKind::Expression(expr),
                    ..
                }) => expr,
                _ => unreachable!(),
            },
            _ => ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, expression_node),
        }
    }

    fn visit_macro_invocation_impl(
        &mut self,
        path: Path<'ast>,
        args: Vec<ExprP<'ast>>,
        span: Span,
    ) -> Result<ExprP<'ast>, AluminaError> {
        use crate::common::CodeErrorBuilder;

        let mut resolver = NameResolver::new();

        let r#macro = match resolver
            .resolve_item(self.scope.clone(), path.clone())
            .with_span(Some(span))?
        {
            ItemResolution::Item(NamedItem {
                kind: NamedItemKind::Macro(symbol, node, scope),
                attributes,
            }) => {
                let mut macro_maker = MacroMaker::new(self.ast, self.global_ctx.clone());
                macro_maker.make(
                    Some(path.segments.last().unwrap().0),
                    symbol,
                    node,
                    scope.clone(),
                    attributes,
                )?;
                symbol
            }
            _ => return Err(CodeErrorKind::NotAMacro(path.to_string())).with_span(Some(span)),
        };

        let result = if self.in_a_macro {
            ExprKind::DeferedMacro(r#macro, args.alloc_on(self.ast)).alloc_with_span(self.ast, span)
        } else {
            let expander =
                MacroExpander::new(self.ast, self.global_ctx.clone(), Some(span), r#macro, args);
            expander.expand()?
        };

        Ok(result)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for ExpressionVisitor<'ast, 'src> {
    type ReturnType = Result<ExprP<'ast>, AluminaError>;

    fn visit_block(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let mut statements = Vec::new();

        let return_expression = with_block_scope!(self, {
            let mut last_node = None;
            for node in node.children_by_field_name("statements", &mut cursor) {
                last_node = Some(node.child_by_field_name("inner").unwrap());
                statements.extend(self.visit_statement(node)?);
            }

            match node.child_by_field_name("result") {
                Some(return_expression) => self.visit(return_expression)?,
                None => {
                    // This is a bit of a hack to work around Tree-Sitter. _expression_ending_with_block nodes
                    // are treated as statements even if they appear in the terminal positions. If they are
                    // actually statements (semicolon), there is another empty_statement inserted, so it's fine.
                    self.extract_expression_ending_with_block(last_node, &mut statements)
                }
            }
        });

        let result = if statements.is_empty() {
            return_expression
        } else {
            let statements = statements.alloc_on(self.ast);
            ExprKind::Block(statements, return_expression).alloc_with_span_from(
                self.ast,
                &self.scope,
                node,
            )
        };

        Ok(result)
    }

    fn visit_closure_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let visitor = ClosureVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            self.scope.anonymous_child(ScopeType::Closure),
            self.in_a_macro,
        );

        let (func, bindings) = visitor.generate(node)?;

        if bindings.is_empty() {
            Ok(
                ExprKind::Fn(FnKind::Normal(func), None).alloc_with_span_from(
                    self.ast,
                    &self.scope,
                    node,
                ),
            )
        } else {
            Ok(
                ExprKind::Fn(FnKind::Closure(bindings, func), None).alloc_with_span_from(
                    self.ast,
                    &self.scope,
                    node,
                ),
            )
        }
    }

    fn visit_integer_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (remainder, kind) = suffixed_literals!(self.code.node_text(node),
            "u8" => BuiltinType::U8,
            "u16" => BuiltinType::U16,
            "u32" => BuiltinType::U32,
            "u64" => BuiltinType::U64,
            "u128" => BuiltinType::U128,
            "i8" => BuiltinType::I8,
            "i16" => BuiltinType::I16,
            "i32" => BuiltinType::I32,
            "i64" => BuiltinType::I64,
            "i128" => BuiltinType::I128,
            "usize" => BuiltinType::USize,
            "isize" => BuiltinType::ISize,
        );

        let value = if remainder.starts_with("0x") {
            u128::from_str_radix(remainder.trim_start_matches("0x"), 16)
        } else if remainder.starts_with("0o") {
            u128::from_str_radix(remainder.trim_start_matches("0o"), 8)
        } else if remainder.starts_with("0b") {
            u128::from_str_radix(remainder.trim_start_matches("0b"), 2)
        } else {
            remainder.parse()
        };

        let value = value
            .map_err(|_| CodeErrorKind::InvalidLiteral)
            .with_span_from(&self.scope, node)?;

        Ok(ExprKind::Lit(Lit::Int(value, kind)).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_float_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (remainder, kind) = suffixed_literals!(self.code.node_text(node),
            "f32" => BuiltinType::F32,
            "f64" => BuiltinType::F64,
        );

        Ok(
            ExprKind::Lit(Lit::Float(remainder.alloc_on(self.ast), kind)).alloc_with_span_from(
                self.ast,
                &self.scope,
                node,
            ),
        )
    }

    fn visit_string_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let s =
            parse_string_literal(self.code.node_text(node)).with_span_from(&self.scope, node)?;

        let s = self.ast.arena.alloc_slice_copy(&s);
        Ok(ExprKind::Lit(Lit::Str(s)).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_char_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let val = match parse_string_literal(self.code.node_text(node))
            .with_span_from(&self.scope, node)?
            .as_slice()
        {
            [v] => *v,
            _ => return Err(CodeErrorKind::InvalidCharLiteral).with_span_from(&self.scope, node),
        };

        Ok(
            ExprKind::Lit(Lit::Int(val as u128, Some(BuiltinType::U8))).alloc_with_span_from(
                self.ast,
                &self.scope,
                node,
            ),
        )
    }

    fn visit_boolean_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self
            .code
            .node_text(node)
            .parse()
            .map_err(|_| CodeErrorKind::InvalidLiteral)
            .with_span_from(&self.scope, node)?;

        Ok(ExprKind::Lit(Lit::Bool(value)).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_ptr_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(ExprKind::Lit(Lit::Null).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_void_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_parenthesized_expression(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        self.visit(node.child_by_field_name("inner").unwrap())
    }

    fn visit_else_clause(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit(node.child_by_field_name("inner").unwrap())
    }

    fn visit_binary_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field_name("left").unwrap())?;
        let op = match self
            .code
            .node_text(node.child_by_field_name("operator").unwrap())
        {
            "&&" => BinOp::And,
            "||" => BinOp::Or,
            "&" => BinOp::BitAnd,
            "|" => BinOp::BitOr,
            "^" => BinOp::BitXor,
            "==" => BinOp::Eq,
            "!=" => BinOp::Neq,
            "<" => BinOp::Lt,
            "<=" => BinOp::LEq,
            ">" => BinOp::Gt,
            ">=" => BinOp::GEq,
            "<<" => BinOp::LShift,
            ">>" => BinOp::RShift,
            "+" => BinOp::Plus,
            "-" => BinOp::Minus,
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,
            _ => unimplemented!(),
        };
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;

        Ok(ExprKind::Binary(op, lhs, rhs).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_assignment_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field_name("left").unwrap())?;
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;

        Ok(ExprKind::Assign(lhs, rhs).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_compound_assignment_expr(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field_name("left").unwrap())?;
        let op = match self
            .code
            .node_text(node.child_by_field_name("operator").unwrap())
        {
            "&&=" => BinOp::And,
            "||=" => BinOp::Or,
            "&=" => BinOp::BitAnd,
            "|=" => BinOp::BitOr,
            "^=" => BinOp::BitXor,
            "<<=" => BinOp::LShift,
            ">>=" => BinOp::RShift,
            "+=" => BinOp::Plus,
            "-=" => BinOp::Minus,
            "*=" => BinOp::Mul,
            "/=" => BinOp::Div,
            "%=" => BinOp::Mod,
            _ => unimplemented!(),
        };
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;
        let result = ExprKind::AssignOp(op, lhs, rhs);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_call_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let func = self.visit(node.child_by_field_name("function").unwrap())?;
        let mut arguments = Vec::new();

        let arguments_node = node.child_by_field_name("arguments").unwrap();
        let mut cursor = arguments_node.walk();
        for node in arguments_node.children_by_field_name("inner", &mut cursor) {
            arguments.push(self.visit(node)?);
        }

        let arguments = arguments.alloc_on(self.ast);
        let result = ExprKind::Call(func, arguments);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_tuple_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field_name("element", &mut cursor) {
            elements.push(self.visit(node)?);
        }

        let result = match elements[..] {
            [] => ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, node),
            _ => {
                let elements = elements.alloc_on(self.ast);
                ExprKind::Tuple(elements).alloc_with_span_from(self.ast, &self.scope, node)
            }
        };

        Ok(result)
    }

    fn visit_try_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let path = PathSegment("try").into();
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: self.scope.code().unwrap().file_id(),
        };
        let inner = self.visit(node.child_by_field_name("inner").unwrap())?;

        self.visit_macro_invocation_impl(path, vec![inner], span)
    }

    fn visit_array_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field_name("element", &mut cursor) {
            elements.push(self.visit(node)?);
        }

        let elements = elements.alloc_on(self.ast);
        let result = ExprKind::Array(elements).alloc_with_span_from(self.ast, &self.scope, node);

        Ok(result)
    }

    fn visit_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_ref(node)
    }

    fn visit_macro_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_macro {
            return Err(CodeErrorKind::DollaredOutsideOfMacro).with_span_from(&self.scope, node);
        }

        self.visit_ref(node)
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_ref(node)
    }

    fn visit_unary_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        let op = match self
            .code
            .node_text(node.child_by_field_name("operator").unwrap())
        {
            "-" => UnOp::Neg,
            "!" => UnOp::Not,
            "~" => UnOp::BitNot,
            _ => unimplemented!(),
        };
        Ok(ExprKind::Unary(op, value).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_reference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(ExprKind::Ref(value).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_dereference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(ExprKind::Deref(value).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_field_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;

        let field = node.child_by_field_name("field").unwrap();
        let field_value = self.code.node_text(field).alloc_on(self.ast);

        let result = match field.kind() {
            "identifier" => {
                let mut resolver = NameResolver::new();
                let unified_fn = match resolver
                    .resolve_item(self.scope.clone(), PathSegment(field_value).into())
                {
                    Ok(ItemResolution::Item(NamedItem {
                        kind: NamedItemKind::Function(item, _, _),
                        ..
                    })) => Some(item),
                    _ => None,
                };

                ExprKind::Field(value, field_value.alloc_on(self.ast), unified_fn)
            }
            "integer_literal" => ExprKind::TupleIndex(value, field_value.parse().unwrap()),
            _ => unreachable!(),
        };

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_index_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        let index = self.visit(node.child_by_field_name("index").unwrap())?;

        let result = ExprKind::Index(value, index);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_range_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lower_bound = node
            .child_by_field_name("lower")
            .map(|n| self.visit(n))
            .transpose()?;
        let upper_bound = node
            .child_by_field_name("upper")
            .map(|n| self.visit(n))
            .transpose()?;

        let result = ExprKind::Range(lower_bound, upper_bound);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_if_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let consequence = self.visit(node.child_by_field_name("consequence").unwrap())?;
        let alternative = match node.child_by_field_name("alternative") {
            Some(node) => self.visit(node)?,
            None => ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, node),
        };

        let condition = node
            .child_by_field_name("condition")
            .map(|n| self.visit(n))
            .transpose()?;

        let result = if let Some(condition) = condition {
            ExprKind::If(condition, consequence, alternative)
        } else {
            let typecheck_node = node.child_by_field_name("type_check").unwrap();
            let typ = TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro)
                .visit(typecheck_node.child_by_field_name("lhs").unwrap())?;
            let bounds = TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro)
                .parse_protocol_bounds(typecheck_node)?;

            let cond = StaticIfCondition { typ, bounds };
            ExprKind::StaticIf(cond, consequence, alternative)
        };

        return Ok(result.alloc_with_span_from(self.ast, &self.scope, node));
    }

    fn visit_generic_function(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let fn_kind = match &self
            .visit(node.child_by_field_name("function").unwrap())?
            .kind
        {
            ExprKind::Fn(fn_kind, None) => fn_kind.clone(),
            ExprKind::Defered(def) => FnKind::Defered(def.clone()),
            _ => {
                //panic!("wow");
                return Err(CodeErrorKind::FunctionExpectedHere).with_span_from(&self.scope, node);
            }
        };

        let mut type_visitor = TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);

        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| type_visitor.visit(child))
            .collect::<Result<Vec<_>, _>>()?
            .alloc_on(self.ast);

        let result = ExprKind::Fn(fn_kind, Some(arguments));
        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_type_cast_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        let typ = TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro)
            .visit(node.child_by_field_name("type").unwrap())?;

        Ok(ExprKind::Cast(value, typ).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_loop_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let was_in_a_loop = std::mem::replace(&mut self.in_a_loop, true);
        let body = self.visit(node.child_by_field_name("body").unwrap());
        self.in_a_loop = was_in_a_loop;
        let body = body?;

        Ok(ExprKind::Loop(body).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_break_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_loop {
            return Err(CodeErrorKind::BreakOutsideOfLoop).with_span_from(&self.scope, node);
        }

        let inner = node
            .child_by_field_name("inner")
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(ExprKind::Break(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_return_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = node
            .child_by_field_name("inner")
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(ExprKind::Return(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_defer_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(ExprKind::Defer(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_continue_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_loop {
            return Err(CodeErrorKind::ContinueOutsideOfLoop).with_span_from(&self.scope, node);
        }
        Ok(ExprKind::Continue.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_for_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let iterable_node = node.child_by_field_name("value").unwrap();
        let iterable = self.visit(iterable_node)?;

        let iterator = self.ast.make_id();
        let iterator_result = self.ast.make_id();

        let id = self.ast.make_id();

        let body = if let Some(name) = node.child_by_field_name("name") {
            let name = self.code.node_text(name).alloc_on(self.ast);

            with_block_scope!(self, {
                self.scope
                    .add_item(Some(name), NamedItem::new_default(NamedItemKind::Local(id)))
                    .with_span_from(&self.scope, node)?;

                let was_in_a_loop = std::mem::replace(&mut self.in_a_loop, true);
                let ret = self.visit(node.child_by_field_name("body").unwrap());
                self.in_a_loop = was_in_a_loop;
                ret?
            })
        } else {
            // Tuple unpacking, i.e. `for (a, b) in ...`
            with_block_scope!(self, {
                let mut statements = Vec::new();
                let mut cursor = node.walk();

                for (idx, elem) in node
                    .children_by_field_name("element", &mut cursor)
                    .enumerate()
                {
                    let name = self.code.node_text(elem).alloc_on(self.ast);
                    let elem_id = self.ast.make_id();

                    let rhs = ExprKind::TupleIndex(
                        ExprKind::Local(id).alloc_with_span_from(self.ast, &self.scope, elem),
                        idx,
                    )
                    .alloc_with_span_from(self.ast, &self.scope, elem);

                    let elem_decl = LetDeclaration {
                        id: elem_id,
                        typ: None,
                        value: Some(rhs),
                    };

                    statements.push(
                        StatementKind::LetDeclaration(elem_decl).alloc_with_span_from(
                            self.ast,
                            &self.scope,
                            node,
                        ),
                    );

                    self.scope
                        .add_item(
                            Some(name),
                            NamedItem::new_default(NamedItemKind::Local(elem_id)),
                        )
                        .with_span_from(&self.scope, elem)?;
                }

                let was_in_a_loop = std::mem::replace(&mut self.in_a_loop, true);
                let ret = self.visit(node.child_by_field_name("body").unwrap());
                self.in_a_loop = was_in_a_loop;

                ExprKind::Block(statements.alloc_on(self.ast), ret?).alloc_with_span_from(
                    self.ast,
                    &self.scope,
                    node,
                )
            })
        };

        // TODO: This is a mess, it should not be so verbose to unsugar a simple for loop
        let mut resolver = NameResolver::new();
        let unified_fn = match resolver.resolve_item(self.scope.clone(), PathSegment("iter").into())
        {
            Ok(ItemResolution::Item(NamedItem {
                kind: NamedItemKind::Function(item, _, _),
                ..
            })) => Some(item),
            _ => None,
        };

        let loop_if = ExprKind::If(
            ExprKind::Field(
                ExprKind::Local(iterator_result).alloc_with_no_span(self.ast),
                "is_some",
                None,
            )
            .alloc_with_no_span(self.ast),
            ExprKind::Block(
                vec![StatementKind::LetDeclaration(LetDeclaration {
                    id,
                    typ: None,
                    value: Some(
                        ExprKind::Field(
                            ExprKind::Local(iterator_result).alloc_with_no_span(self.ast),
                            "inner",
                            None,
                        )
                        .alloc_with_no_span(self.ast),
                    ),
                })
                .alloc_with_no_span(self.ast)]
                .alloc_on(self.ast),
                body,
            )
            .alloc_with_no_span(self.ast),
            ExprKind::Break(None).alloc_with_no_span(self.ast),
        );

        let loop_body = ExprKind::Loop(
            ExprKind::Block(
                vec![StatementKind::LetDeclaration(LetDeclaration {
                    id: iterator_result,
                    typ: None,
                    value: Some(
                        ExprKind::Call(
                            ExprKind::Field(
                                ExprKind::Local(iterator).alloc_with_no_span(self.ast),
                                "next",
                                None,
                            )
                            .alloc_with_no_span(self.ast),
                            vec![].alloc_on(self.ast),
                        )
                        .alloc_with_no_span(self.ast),
                    ),
                })
                .alloc_with_no_span(self.ast)]
                .alloc_on(self.ast),
                loop_if.alloc_with_no_span(self.ast),
            )
            .alloc_with_span_from(self.ast, &self.scope, node),
        );

        let result = ExprKind::Block(
            vec![StatementKind::LetDeclaration(LetDeclaration {
                id: iterator,
                typ: None,
                value: Some(
                    ExprKind::Call(
                        ExprKind::Field(iterable, "iter", unified_fn).alloc_with_span_from(
                            self.ast,
                            &self.scope,
                            iterable_node,
                        ),
                        [].alloc_on(self.ast),
                    )
                    .alloc_with_span_from(self.ast, &self.scope, iterable_node),
                ),
            })
            .alloc_with_span_from(self.ast, &self.scope, node)]
            .alloc_on(self.ast),
            loop_body.alloc_with_no_span(self.ast),
        );

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_switch_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;

        let mut arms = Vec::new();
        let mut default_arm = None;

        let body = node.child_by_field_name("body").unwrap();
        let mut cursor = body.walk();

        // Switch is desugared into a series of if-else expressions
        for arm in body.children_by_field_name("arm", &mut cursor) {
            if default_arm.is_some() {
                return Err(CodeErrorKind::DefaultCaseMustBeLast).with_span_from(&self.scope, arm);
            }

            let pattern = arm.child_by_field_name("pattern").unwrap();
            let mut cursor = pattern.walk();

            let alternatives = pattern
                .children_by_field_name("value", &mut cursor)
                .map(|child| self.visit(child))
                .collect::<Result<Vec<_>, _>>()?;

            if !alternatives.is_empty() {
                arms.push((
                    arm,
                    alternatives,
                    self.visit(arm.child_by_field_name("value").unwrap())?,
                ))
            } else {
                default_arm = Some(self.visit(arm.child_by_field_name("value").unwrap())?);
            }
        }

        let local_id = self.ast.make_id();
        let local = ExprKind::Local(local_id).alloc_with_span_from(self.ast, &self.scope, node);
        let stmts = vec![StatementKind::LetDeclaration(LetDeclaration {
            id: local_id,
            typ: None,
            value: Some(value),
        })
        .alloc_with_no_span(self.ast)];

        let ret = arms.into_iter().rfold(
            default_arm.unwrap_or_else(|| ExprKind::Void.alloc_with_no_span(self.ast)),
            |acc, (arm_node, alternatives, value)| {
                // TODO: add spans here
                let cmp = alternatives
                    .into_iter()
                    .fold(None, |acc, alternative| match acc {
                        Some(acc) => Some(
                            ExprKind::Binary(
                                BinOp::Or,
                                acc,
                                ExprKind::Binary(BinOp::Eq, local, alternative)
                                    .alloc_with_no_span(self.ast),
                            )
                            .alloc_with_no_span(self.ast),
                        ),
                        None => Some(
                            ExprKind::Binary(BinOp::Eq, local, alternative)
                                .alloc_with_no_span(self.ast),
                        ),
                    })
                    .unwrap();
                let branch = ExprKind::If(cmp, value, acc);

                branch.alloc_with_span_from(self.ast, &self.scope, arm_node)
            },
        );

        let block = ExprKind::Block(stmts.alloc_on(self.ast), ret).alloc_with_span_from(
            self.ast,
            &self.scope,
            node,
        );

        Ok(block)
    }

    fn visit_struct_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let typ = TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro)
            .visit(node.child_by_field_name("name").unwrap())?;

        let initializer_node = node.child_by_field_name("arguments").unwrap();
        let mut field_initializers = Vec::new();
        let mut names = HashSet::new();

        with_block_scope!(self, {
            let mut cursor = initializer_node.walk();

            for node in initializer_node.children_by_field_name("item", &mut cursor) {
                let name = self
                    .code
                    .node_text(node.child_by_field_name("field").unwrap());

                if !names.insert(name) {
                    return Err(CodeErrorKind::DuplicateFieldInitializer(name.to_string()))
                        .with_span_from(&self.scope, node);
                }

                let value = self.visit(node.child_by_field_name("value").unwrap())?;

                let span = Span {
                    start: node.start_byte(),
                    end: node.end_byte(),
                    file: self.scope.code().unwrap().file_id(),
                };

                field_initializers.push(FieldInitializer {
                    name: name.alloc_on(self.ast),
                    value,
                    span: Some(span),
                });
            }
        });

        Ok(
            ExprKind::Struct(typ, field_initializers.alloc_on(self.ast)).alloc_with_span_from(
                self.ast,
                &self.scope,
                node,
            ),
        )
    }

    fn visit_while_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let condition = self.visit(node.child_by_field_name("condition").unwrap())?;

        let was_in_a_loop = std::mem::replace(&mut self.in_a_loop, true);
        let body = self.visit(node.child_by_field_name("body").unwrap());
        self.in_a_loop = was_in_a_loop;
        let body = body?;

        let r#break = ExprKind::Break(None).alloc_with_span_from(self.ast, &self.scope, node);
        let body = ExprKind::If(condition, body, r#break).alloc_with_span_from(
            self.ast,
            &self.scope,
            node,
        );

        Ok(ExprKind::Loop(body).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_et_cetera_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_macro {
            return Err(CodeErrorKind::EtCeteraOutsideOfMacro).with_span_from(&self.scope, node);
        }

        if !self.has_et_cetera {
            return Err(CodeErrorKind::NoEtCeteraArgs).with_span_from(&self.scope, node);
        }

        let inner = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(ExprKind::EtCetera(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_macro_invocation(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);
        let path = visitor.visit(node.child_by_field_name("macro").unwrap())?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: self.scope.code().unwrap().file_id(),
        };

        let mut arguments = Vec::new();
        let arguments_node = node.child_by_field_name("arguments").unwrap();
        let mut cursor = arguments_node.walk();
        for node in arguments_node.children_by_field_name("inner", &mut cursor) {
            arguments.push(self.visit(node)?);
        }

        self.visit_macro_invocation_impl(path, arguments, span)
    }

    fn visit_universal_macro_invocation(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);
        let path = visitor.visit(node.child_by_field_name("macro").unwrap())?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: self.scope.code().unwrap().file_id(),
        };

        let mut arguments = Vec::new();
        arguments.push(self.visit(node.child_by_field_name("value").unwrap())?);

        let arguments_node = node.child_by_field_name("arguments").unwrap();
        let mut cursor = arguments_node.walk();

        for node in arguments_node.children_by_field_name("inner", &mut cursor) {
            arguments.push(self.visit(node)?);
        }
        self.visit_macro_invocation_impl(path, arguments, span)
    }
}

pub fn parse_string_literal(lit: &str) -> Result<Vec<u8>, CodeErrorKind> {
    let mut result = Vec::<u8>::with_capacity(lit.len());

    enum State {
        Normal,
        Escape,
        Hex,
        UnicodeStart,
        UnicodeShort,
        UnicodeLong,
    }

    let mut state = State::Normal;
    let mut buf = String::with_capacity(4);

    for ch in lit[1..lit.len() - 1].bytes() {
        state = match state {
            State::Normal => match ch {
                b'\\' => State::Escape,
                _ => {
                    result.push(ch);
                    State::Normal
                }
            },
            State::Escape => match ch {
                b'\\' => {
                    result.push(b'\\');
                    State::Normal
                }
                b'n' => {
                    result.push(b'\n');
                    State::Normal
                }
                b'r' => {
                    result.push(b'\r');
                    State::Normal
                }
                b't' => {
                    result.push(b'\t');
                    State::Normal
                }
                b'\'' => {
                    result.push(b'\'');
                    State::Normal
                }
                b'"' => {
                    result.push(b'"');
                    State::Normal
                }
                b'0' => {
                    result.push(b'\0');
                    State::Normal
                }
                b'x' => State::Hex,
                b'u' => State::UnicodeStart,
                _ => {
                    return Err(CodeErrorKind::InvalidEscapeSequence);
                }
            },
            State::Hex => {
                if buf.len() == 1 {
                    buf.push(ch as char);
                    let ch = u8::from_str_radix(&buf, 16).unwrap();
                    result.push(ch);
                    buf.clear();
                    State::Normal
                } else {
                    buf.push(ch as char);
                    State::Hex
                }
            }
            State::UnicodeStart => match ch {
                b'{' => State::UnicodeLong,
                _ => {
                    buf.push(ch as char);
                    State::UnicodeShort
                }
            },
            State::UnicodeShort => {
                if buf.len() == 3 {
                    buf.push(ch as char);
                    let ch = u32::from_str_radix(&buf, 16).unwrap();
                    let utf8 = char::from_u32(ch)
                        .ok_or(CodeErrorKind::InvalidEscapeSequence)?
                        .to_string();

                    result.extend(utf8.as_bytes());
                    buf.clear();
                    State::Normal
                } else {
                    buf.push(ch as char);
                    State::UnicodeShort
                }
            }
            State::UnicodeLong => match ch {
                b'}' => {
                    let ch = u32::from_str_radix(&buf, 16).unwrap();
                    let utf8 = char::from_u32(ch)
                        .ok_or(CodeErrorKind::InvalidEscapeSequence)?
                        .to_string();
                    result.extend(utf8.as_bytes());
                    buf.clear();
                    State::Normal
                }
                _ => {
                    buf.push(ch as char);
                    State::UnicodeShort
                }
            },
        };
    }

    match state {
        State::Normal => Ok(result),
        _ => Err(CodeErrorKind::InvalidEscapeSequence),
    }
}

pub struct ClosureVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    self_param: AstId,

    parameters: Vec<Parameter<'ast>>,
    bound_values: HashMap<AstId, (BoundItemType, ExprP<'ast>)>,
    placeholders: Vec<Placeholder<'ast>>,
    return_type: Option<TyP<'ast>>,
    body: Option<ExprP<'ast>>,
    in_a_macro: bool,
}

impl<'ast, 'src> ClosureVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        global_ctx: GlobalCtx,
        scope: Scope<'ast, 'src>,
        in_a_macro: bool,
    ) -> Self {
        Self {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            global_ctx,
            self_param: ast.make_id(),
            parameters: Vec::new(),
            placeholders: Vec::new(),
            bound_values: HashMap::new(),
            return_type: None,
            body: None,
            in_a_macro,
        }
    }

    pub fn generate(
        mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<(ItemP<'ast>, &'ast [ClosureBinding<'ast>]), AluminaError> {
        self.visit(node)?;

        let symbol = self.ast.make_symbol();
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: self.scope.code().unwrap().file_id(),
        };

        if !self.bound_values.is_empty() {
            let placeholder = self.ast.make_id();
            self.placeholders.push(Placeholder {
                id: placeholder,
                bounds: [].alloc_on(self.ast),
                default: None,
            });

            let span = Span {
                start: node.start_byte(),
                end: node.end_byte(),
                file: self.scope.code().unwrap().file_id(),
            };

            // Closure struct is passed by a mutable pointer
            let placeholder_ty = self.ast.intern_type(Ty::Placeholder(placeholder));
            self.parameters.insert(
                0,
                Parameter {
                    id: self.self_param,
                    typ: self.ast.intern_type(Ty::Pointer(placeholder_ty, false)),
                    span: Some(span),
                },
            );
        }

        symbol.assign(Item::Function(Function {
            name: None,
            attributes: [].alloc_on(self.ast),
            placeholders: self.placeholders.alloc_on(self.ast),
            args: self.parameters.alloc_on(self.ast),
            return_type: self.return_type.unwrap(),
            body: Some(self.body.unwrap()),
            varargs: false,
            span: Some(span),
            lambda: true,
            is_protocol_fn: false,
        }));

        let bindings = self
            .bound_values
            .iter()
            .map(|(k, (t, v))| super::ClosureBinding {
                id: *k,
                value: *v,
                binding_type: *t,
            })
            .collect::<Vec<_>>()
            .alloc_on(self.ast);

        Ok((symbol, bindings))
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for ClosureVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_parameter(&mut self, node: tree_sitter::Node<'src>) -> Result<(), AluminaError> {
        let name_node = node.child_by_field_name("name").unwrap();
        let name = self.code.node_text(name_node).alloc_on(self.ast);
        let id = self.ast.make_id();

        self.scope
            .add_item(
                Some(name),
                NamedItem::new_default(NamedItemKind::Parameter(id, node)),
            )
            .with_span_from(&self.scope, node)?;

        let field_type = TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro)
            .visit(node.child_by_field_name("type").unwrap())?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: self.scope.code().unwrap().file_id(),
        };

        self.parameters.push(Parameter {
            id,
            typ: field_type,
            span: Some(span),
        });

        Ok(())
    }

    fn visit_bound_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self
            .code
            .node_text(node.child_by_field_name("name").unwrap())
            .alloc_on(self.ast)
            .trim_start_matches('@');

        let bound_type = if let Some(_) = node.child_by_field_name("by_reference") {
            BoundItemType::ByReference
        } else {
            BoundItemType::ByValue
        };

        let mut resolver = NameResolver::new();
        let original = match resolver
            .resolve_item(self.scope.parent().unwrap(), PathSegment(name).into())
            .with_span_from(&self.scope, node)?
        {
            ItemResolution::Item(NamedItem {
                kind: NamedItemKind::Local(id) | NamedItemKind::Parameter(id, _),
                ..
            }) => ExprKind::Local(id),
            ItemResolution::Item(NamedItem {
                kind: NamedItemKind::BoundValue(self_arg, id, bound_type),
                ..
            }) => ExprKind::BoundParam(self_arg, id, bound_type),
            _ => {
                return Err(CodeErrorKind::CanOnlyCloseOverLocals).with_span_from(&self.scope, node)
            }
        };

        let id = self.ast.make_id();
        self.scope
            .add_item(
                Some(name),
                NamedItem::new_default(NamedItemKind::BoundValue(self.self_param, id, bound_type)),
            )
            .with_span_from(&self.scope, node)?;

        self.bound_values.insert(
            id,
            (
                bound_type,
                original.alloc_with_span_from(self.ast, &self.scope, node),
            ),
        );

        Ok(())
    }

    fn visit_closure_parameters(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();

        for param in node.children_by_field_name("parameter", &mut cursor) {
            self.visit(param)?
        }

        Ok(())
    }

    fn visit_closure_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit(node.child_by_field_name("parameters").unwrap())?;

        self.body = Some(
            ExpressionVisitor::new(
                self.ast,
                self.global_ctx.clone(),
                self.scope.clone(),
                self.in_a_macro,
            )
            .generate(node.child_by_field_name("body").unwrap())?,
        );

        self.return_type = Some(
            node.child_by_field_name("return_type")
                .map(|node| {
                    TypeVisitor::new(self.ast, self.scope.clone(), self.in_a_macro).visit(node)
                })
                .transpose()?
                .unwrap_or_else(|| self.ast.intern_type(Ty::Builtin(BuiltinType::Void))),
        );

        Ok(())
    }
}
