use crate::ast::macros::{MacroExpander, MacroMaker};
use crate::ast::maker::AstItemMaker;
use crate::ast::types::TypeVisitor;
use crate::ast::{
    AstCtx, BinOp, BuiltinType, ClosureBinding, Defered, Expr, ExprKind, ExprP, FieldInitializer,
    FnKind, Function, Id, Item, ItemP, LetDeclaration, Lit, Parameter, Placeholder, Span,
    Statement, StatementKind, StaticForLoopVariable, Ty, TyP, UnOp,
};
use crate::common::{
    AluminaError, ArenaAllocatable, CodeDiagnostic, CodeErrorBuilder, HashSet,
    WithSpanDuringParsing,
};
use crate::global_ctx::GlobalCtx;
use crate::parser::{AluminaVisitor, FieldKind, NodeExt, NodeKind, ParseCtx};
use crate::src::pass1::FirstPassVisitor;
use crate::src::path::{Path, PathSegment};
use crate::src::resolver::{ItemResolution, NameResolver};
use crate::src::scope::{BoundItemType, NamedItem, NamedItemKind, Scope, ScopeType};
use crate::visitors::{AttributeVisitor, ScopedPathVisitor};

use crate::common::IndexMap;

use super::MacroCtx;

macro_rules! with_block_scope {
    ($self:ident, $body:expr) => {{
        let child_scope = $self.scope.anonymous_child(ScopeType::Block);
        let previous_scope = std::mem::replace(&mut $self.scope, child_scope.clone());
        previous_scope
            .add_item(
                None,
                NamedItem::new_no_node(NamedItemKind::Anonymous, Some(child_scope)),
            )
            .unwrap();
        let result = $body;
        $self.scope.check_unused_items(&$self.global_ctx.diag());
        $self.scope = previous_scope;
        result
    }};
}

trait Spannable<'ast, 'src>
where
    Self: Sized,
{
    type ReturnType;
    fn alloc_with_span(self, ast: &'ast AstCtx<'ast>, span: Option<Span>) -> Self::ReturnType;

    fn alloc_with_span_from(
        self,
        ast: &'ast AstCtx<'ast>,
        scope: &Scope<'ast, 'src>,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let span = Span::from_node(scope.code().unwrap().file_id(), node);
        self.alloc_with_span(ast, Some(span))
    }
}

impl<'ast, 'src> Spannable<'ast, 'src> for ExprKind<'ast> {
    type ReturnType = ExprP<'ast>;

    fn alloc_with_span(self, ast: &'ast AstCtx<'ast>, span: Option<Span>) -> ExprP<'ast> {
        Expr { kind: self, span }.alloc_on(ast)
    }
}

impl<'ast, 'src> Spannable<'ast, 'src> for StatementKind<'ast> {
    type ReturnType = Statement<'ast>;

    fn alloc_with_span(self, _ast: &'ast AstCtx<'ast>, span: Option<Span>) -> Statement<'ast> {
        Statement { kind: self, span }
    }
}

pub struct ExpressionVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    global_ctx: GlobalCtx,
    scope: Scope<'ast, 'src>,
    macro_ctx: MacroCtx,
}

macro_rules! suffixed_literals {
    ($e:expr, $($suffix:literal => $ty:path),+) => {
        match $e {
            $(
                v if v.ends_with($suffix) => (&v[..v.len() - $suffix.len()], Some($ty)),
            )+
            v => (v, None)
        }
    };
    ($e:expr, $($suffix:literal => $ty:path,)+) => {
        suffixed_literals!($e, $($suffix => $ty),+)
    };
}

impl<'ast, 'src> ExpressionVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        global_ctx: GlobalCtx,
        scope: Scope<'ast, 'src>,
        macro_ctx: MacroCtx,
    ) -> Self {
        ExpressionVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            global_ctx,
            macro_ctx,
        }
    }

    pub fn generate(mut self, node: tree_sitter::Node<'src>) -> Result<ExprP<'ast>, AluminaError> {
        let result = self.visit(node)?;
        Ok(result)
    }

    fn visit_ref(&mut self, node: tree_sitter::Node<'src>) -> Result<ExprP<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.macro_ctx);
        let path = visitor.visit(node)?;

        resolve_name(
            self.global_ctx.clone(),
            self.ast,
            &self.scope,
            path,
            Some(Span::from_node(self.scope.file_id(), node)),
        )
    }

    fn visit_let_declaration(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<Vec<Statement<'ast>>, AluminaError> {
        let ty = node
            .child_by_field(FieldKind::Type)
            .map(|n| {
                TypeVisitor::new(
                    self.global_ctx.clone(),
                    self.ast,
                    self.scope.clone(),
                    self.macro_ctx,
                )
                .visit(n)
            })
            .transpose()?;
        let value_id = self.ast.make_id();
        let value = node
            .child_by_field(FieldKind::Value)
            .map(|n| self.visit(n))
            .transpose()?;
        let let_decl = LetDeclaration {
            id: value_id,
            ty,
            value,
        };
        let mut statements = Vec::new();
        if let Some(name_node) = node.child_by_field(FieldKind::Name) {
            let name = self.code.node_text(name_node).alloc_on(self.ast);
            self.ast.add_local_name(value_id, name);
            self.scope
                .add_item(
                    Some(name),
                    NamedItem::new_default(NamedItemKind::Local(value_id), name_node, None),
                )
                .with_span_from(&self.scope, node)?;

            statements.push(
                StatementKind::LetDeclaration(let_decl).alloc_with_span_from(
                    self.ast,
                    &self.scope,
                    node,
                ),
            );
        } else {
            // Tuple unpacking
            let mut cursor = node.walk();
            for (idx, name_node) in node
                .children_by_field(FieldKind::Element, &mut cursor)
                .enumerate()
            {
                let name = self.code.node_text(name_node).alloc_on(self.ast);
                let elem_id = self.ast.make_id();

                let rhs = ExprKind::TupleIndex(
                    ExprKind::Local(value_id).alloc_with_span_from(
                        self.ast,
                        &self.scope,
                        name_node,
                    ),
                    ExprKind::Lit(Lit::Int(false, idx as u128, Some(BuiltinType::USize)))
                        .alloc_with_span_from(self.ast, &self.scope, name_node),
                )
                .alloc_with_span_from(self.ast, &self.scope, name_node);

                let elem_decl = LetDeclaration {
                    id: elem_id,
                    ty: None,
                    value: Some(rhs),
                };

                statements.push(
                    StatementKind::LetDeclaration(elem_decl).alloc_with_span_from(
                        self.ast,
                        &self.scope,
                        node,
                    ),
                );

                self.ast.add_local_name(elem_id, name);
                self.scope
                    .add_item(
                        Some(name),
                        NamedItem::new_default(NamedItemKind::Local(elem_id), name_node, None),
                    )
                    .with_span_from(&self.scope, name_node)?;
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
        Ok(statements)
    }

    fn extract_expression_ending_with_block(
        &self,
        last_node: Option<tree_sitter::Node<'src>>,
        statements: &mut Vec<Statement<'ast>>,
    ) -> Result<ExprP<'ast>, AluminaError> {
        let last_node = match last_node {
            Some(n) => n,
            None => return Ok(ExprKind::Void.alloc_with_span(self.ast, None)),
        };

        let expression_node = match last_node.kind_typed() {
            NodeKind::ExpressionStatement => last_node.child_by_field(FieldKind::Inner).unwrap(),
            _ => return Ok(ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, last_node)),
        };

        match expression_node.kind_typed() {
            NodeKind::Block
            | NodeKind::IfExpression
            | NodeKind::SwitchExpression
            | NodeKind::WhileExpression
            | NodeKind::LoopExpression
            | NodeKind::StaticForExpression
            | NodeKind::ForExpression => match statements.pop() {
                Some(Statement {
                    kind: StatementKind::Expression(expr),
                    ..
                }) => Ok(expr),
                _ => {
                    // There are no statements preceeding the return expression. From the pure syntax perspective this
                    // should not be possible, however we may have filtered a statement out due to #[cfg] directive on it.
                    Ok(ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, expression_node))
                }
            },
            _ => Ok(ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, expression_node)),
        }
    }

    fn visit_macro_invocation_impl(
        &mut self,
        path: Path<'ast>,
        args: Vec<ExprP<'ast>>,
        span: Span,
    ) -> Result<ExprP<'ast>, AluminaError> {
        let mut resolver = NameResolver::new();

        let r#macro = match resolver
            .resolve_item(self.scope.clone(), path.clone())
            .with_span(Some(span))?
        {
            ItemResolution::Item(NamedItem {
                kind: NamedItemKind::Macro(item),
                attributes,
                node,
                scope,
            }) => {
                if let (Some(node), Some(scope)) = (node, scope) {
                    let mut macro_maker = MacroMaker::new(self.ast, self.global_ctx.clone());
                    macro_maker.make(
                        Some(path.segments.last().unwrap().0),
                        item,
                        node,
                        scope.clone(),
                        attributes,
                    )?;
                }
                item
            }
            _ => return Err(CodeDiagnostic::NotAMacro).with_span(Some(span)),
        };

        let result = if self.macro_ctx.in_a_macro {
            ExprKind::MacroInvocation(
                ExprKind::Macro(r#macro, &[]).alloc_with_span(self.ast, Some(span)),
                args.alloc_on(self.ast),
            )
            .alloc_with_span(self.ast, Some(span))
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

        let mut item_name = None;
        let mut local_items: IndexMap<_, Vec<_>> = IndexMap::default();

        macro_rules! make_stuff {
            () => {
                if !local_items.is_empty() {
                    let local_items = std::mem::take(&mut local_items);
                    let mut maker =
                        AstItemMaker::new_local(self.ast, self.global_ctx.clone(), self.macro_ctx);
                    for (name, items) in local_items.into_iter() {
                        maker.make_item_group(self.scope.clone(), name, &items[..])?;
                    }
                }
            };
        }

        let return_expression = with_block_scope!(self, {
            let mut last_node = None;
            for node in node.children_by_field(FieldKind::Statements, &mut cursor) {
                last_node = Some(node.child_by_field(FieldKind::Inner).unwrap());

                let node = node.child_by_field(FieldKind::Inner).unwrap();
                match AttributeVisitor::parse_attributes(
                    self.global_ctx.clone(),
                    self.ast,
                    self.scope.clone(),
                    node,
                    None,
                )? {
                    Some(attributes) => attributes,
                    None => continue,
                };

                let result = match node.kind_typed() {
                    NodeKind::EmptyStatement => vec![],
                    NodeKind::LetDeclaration => self.visit_let_declaration(node)?,
                    NodeKind::ExpressionStatement => vec![StatementKind::Expression(
                        self.visit(node.child_by_field(FieldKind::Inner).unwrap())?,
                    )
                    .alloc_with_span_from(self.ast, &self.scope, node)],
                    NodeKind::EnumDefinition
                    | NodeKind::StructDefinition
                    | NodeKind::ProtocolDefinition
                    | NodeKind::ImplBlock
                    | NodeKind::MacroDefinition
                    | NodeKind::ConstDeclaration
                    | NodeKind::StaticDeclaration
                    | NodeKind::TypeDefinition
                    | NodeKind::FunctionDefinition
                    | NodeKind::UseDeclaration => {
                        // In linear scopes named items must be declared first, followed by their impl blocks (with no other
                        // items in between).
                        // In module scopes, this restriction does not apply.
                        match node.kind_typed() {
                            NodeKind::EnumDefinition
                            | NodeKind::StructDefinition
                            | NodeKind::ProtocolDefinition => {
                                make_stuff!();
                                item_name = Some(
                                    self.code
                                        .node_text(node.child_by_field(FieldKind::Name).unwrap()),
                                );
                            }
                            NodeKind::ImplBlock => {
                                let name = Some(
                                    self.code
                                        .node_text(node.child_by_field(FieldKind::Name).unwrap()),
                                );
                                if name != item_name {
                                    make_stuff!();
                                    item_name = name;
                                }
                            }
                            _ => {
                                make_stuff!();
                                item_name = None;
                            }
                        };

                        let items = FirstPassVisitor::new(
                            self.global_ctx.clone(),
                            self.ast,
                            self.scope.clone(),
                            self.macro_ctx,
                        )
                        .visit_local(node)?;

                        if !items.is_empty() && self.macro_ctx.in_a_macro {
                            return Err(CodeDiagnostic::MacrosCannotDefineItems)
                                .with_span_from(&self.scope, node);
                        }

                        for ((scope, name), values) in items.into_iter() {
                            if scope != self.scope {
                                continue;
                            }

                            local_items.entry(name).or_default().extend(values);
                        }

                        vec![]
                    }
                    _ => unreachable!(),
                };

                statements.extend(result);
            }

            make_stuff!();

            let ret = match node.child_by_field(FieldKind::Result) {
                Some(return_expression) => self.visit(return_expression)?,
                None => {
                    // This is a bit of a hack to work around Tree-Sitter. _expression_ending_with_block nodes
                    // are treated as statements even if they appear in the terminal positions. If they are
                    // actually statements (semicolon), there is another empty_statement inserted, so it's fine.
                    self.extract_expression_ending_with_block(last_node, &mut statements)?
                }
            };
            ret
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

    fn visit_lambda_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if self.macro_ctx.in_a_macro {
            return Err(CodeDiagnostic::MacrosCannotDefineLambdas)
                .with_span_from(&self.scope, node);
        }

        let child_scope = self.scope.anonymous_child(ScopeType::Closure);
        let visitor = LambdaVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            child_scope.clone(),
            self.macro_ctx,
        );

        let (func, bindings) = visitor.generate(node)?;

        self.scope
            .add_item(
                None,
                NamedItem::new_no_node(NamedItemKind::Closure(func), Some(child_scope)),
            )
            .unwrap();

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
        let (mut remainder, kind) = suffixed_literals!(self.code.node_text(node),
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

        let sign = if remainder.starts_with('-') {
            remainder = &remainder[1..];
            true
        } else {
            false
        };

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
            .map_err(|_| CodeDiagnostic::InvalidLiteral)
            .with_span_from(&self.scope, node)?;

        Ok(
            ExprKind::Lit(Lit::Int(sign, value, kind)).alloc_with_span_from(
                self.ast,
                &self.scope,
                node,
            ),
        )
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
            _ => return Err(CodeDiagnostic::InvalidCharLiteral).with_span_from(&self.scope, node),
        };

        Ok(
            ExprKind::Lit(Lit::Int(false, val as u128, Some(BuiltinType::U8)))
                .alloc_with_span_from(self.ast, &self.scope, node),
        )
    }

    fn visit_boolean_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self
            .code
            .node_text(node)
            .parse()
            .map_err(|_| CodeDiagnostic::InvalidLiteral)
            .with_span_from(&self.scope, node)?;

        Ok(ExprKind::Lit(Lit::Bool(value)).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_ptr_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(ExprKind::Lit(Lit::Null).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_parenthesized_expression(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        self.visit(node.child_by_field(FieldKind::Inner).unwrap())
    }

    fn visit_else_clause(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit(node.child_by_field(FieldKind::Inner).unwrap())
    }

    fn visit_binary_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field(FieldKind::Left).unwrap())?;
        let op = match self
            .code
            .node_text(node.child_by_field(FieldKind::Operator).unwrap())
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
        let rhs = self.visit(node.child_by_field(FieldKind::Right).unwrap())?;

        Ok(ExprKind::Binary(op, lhs, rhs).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_assignment_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field(FieldKind::Left).unwrap())?;
        let rhs = self.visit(node.child_by_field(FieldKind::Right).unwrap())?;

        Ok(ExprKind::Assign(lhs, rhs).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_compound_assignment_expr(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field(FieldKind::Left).unwrap())?;
        let op = match self
            .code
            .node_text(node.child_by_field(FieldKind::Operator).unwrap())
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
        let rhs = self.visit(node.child_by_field(FieldKind::Right).unwrap())?;
        let result = ExprKind::AssignOp(op, lhs, rhs);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_call_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let func = self.visit(node.child_by_field(FieldKind::Function).unwrap())?;
        let mut arguments = Vec::new();

        let arguments_node = node.child_by_field(FieldKind::Arguments).unwrap();
        let mut cursor = arguments_node.walk();
        for node in arguments_node.children_by_field(FieldKind::Inner, &mut cursor) {
            arguments.push(self.visit(node)?);
        }

        let arguments = arguments.alloc_on(self.ast);
        let result = ExprKind::Call(func, arguments);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_tuple_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field(FieldKind::Element, &mut cursor) {
            if node.kind_typed() == NodeKind::EtCeteraExpression
                && node.child_by_field(FieldKind::Tuple).is_some()
            {
                let value = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;
                elements.push(ExprKind::EtCetera(value).alloc_with_span_from(
                    self.ast,
                    &self.scope,
                    node,
                ));
            } else {
                elements.push(self.visit(node)?);
            }
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
        let span = Span::from_node(self.scope.file_id(), node);
        let inner = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;

        self.visit_macro_invocation_impl(path, vec![inner], span)
    }

    fn visit_array_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field(FieldKind::Element, &mut cursor) {
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
        if !self.macro_ctx.in_a_macro {
            return Err(CodeDiagnostic::DollaredOutsideOfMacro).with_span_from(&self.scope, node);
        }

        self.visit_ref(node)
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_ref(node)
    }

    fn visit_unary_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        let op = match self
            .code
            .node_text(node.child_by_field(FieldKind::Operator).unwrap())
        {
            "-" => UnOp::Neg,
            "!" => UnOp::Not,
            "~" => UnOp::BitNot,
            _ => unimplemented!(),
        };
        Ok(ExprKind::Unary(op, value).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_reference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        Ok(ExprKind::Ref(value).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_dereference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        Ok(ExprKind::Deref(value).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_field_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        let field = node.child_by_field(FieldKind::Field).unwrap();

        let result = match field.kind_typed() {
            NodeKind::Identifier => {
                let field_value = self.code.node_text(field).alloc_on(self.ast);
                let mut resolver = NameResolver::new();
                let unified_fn = match resolver
                    .resolve_item(self.scope.clone(), PathSegment(field_value).into())
                {
                    Ok(ItemResolution::Item(NamedItem {
                        kind: NamedItemKind::Function(item),
                        ..
                    })) => Some(item),
                    _ => None,
                };

                ExprKind::Field(value, field_value.alloc_on(self.ast), unified_fn, None)
            }

            _ => ExprKind::TupleIndex(value, self.visit(field)?),
        };

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_tuple_index_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit(node.child_by_field(FieldKind::Field).unwrap())
    }

    fn visit_index_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        let index = self.visit(node.child_by_field(FieldKind::Index).unwrap())?;

        let result = ExprKind::Index(value, index);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_range_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lower_bound = node
            .child_by_field(FieldKind::Lower)
            .map(|n| self.visit(n))
            .transpose()?;
        let upper_bound = node
            .child_by_field(FieldKind::Upper)
            .map(|n| self.visit(n))
            .transpose()?;

        let inclusive = node
            .child_by_field(FieldKind::Inclusive)
            .map(|n| self.code.node_text(n) == "..=")
            .unwrap_or(false);

        let result = ExprKind::Range(lower_bound, upper_bound, inclusive);

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_if_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let consequence = self.visit(node.child_by_field(FieldKind::Consequence).unwrap())?;
        let alternative = match node.child_by_field(FieldKind::Alternative) {
            Some(node) => self.visit(node)?,
            None => ExprKind::Void.alloc_with_span_from(self.ast, &self.scope, node),
        };

        let condition = self.visit(node.child_by_field(FieldKind::Condition).unwrap())?;

        let result = match self
            .code
            .node_text(node.child_by_field(FieldKind::Kind).unwrap())
        {
            "if" => ExprKind::If(condition, consequence, alternative),
            "when" => ExprKind::StaticIf(condition, consequence, alternative),
            _ => unreachable!(),
        };

        return Ok(result.alloc_with_span_from(self.ast, &self.scope, node));
    }

    fn visit_type_check_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        let ty = TypeVisitor::new(
            self.global_ctx.clone(),
            self.ast,
            self.scope.clone(),
            self.macro_ctx,
        )
        .visit(node.child_by_field(FieldKind::Type).unwrap())?;

        Ok(ExprKind::TypeCheck(lhs, ty).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_turbofish(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut type_visitor = TypeVisitor::new(
            self.global_ctx.clone(),
            self.ast,
            self.scope.clone(),
            self.macro_ctx,
        );

        let arguments_node = node.child_by_field(FieldKind::TypeArguments).unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field(FieldKind::Type, &mut cursor)
            .map(|child| type_visitor.visit(child))
            .collect::<Result<Vec<_>, _>>()?
            .alloc_on(self.ast);

        let fn_kind = match &self
            .visit(node.child_by_field(FieldKind::Function).unwrap())?
            .kind
        {
            ExprKind::Fn(fn_kind, None) => *fn_kind,
            ExprKind::Defered(def) => FnKind::Defered(*def),
            ExprKind::Static(inner, None) => {
                let ret = ExprKind::Static(inner, Some(arguments));
                return Ok(ret.alloc_with_span_from(self.ast, &self.scope, node));
            }
            ExprKind::Const(inner, None) => {
                let ret = ExprKind::Const(inner, Some(arguments));
                return Ok(ret.alloc_with_span_from(self.ast, &self.scope, node));
            }
            ExprKind::Field(base, field, unified_fn, generic_args) => {
                assert!(generic_args.is_none());

                let ret = ExprKind::Field(base, field, *unified_fn, Some(arguments));
                return Ok(ret.alloc_with_span_from(self.ast, &self.scope, node));
            }
            _ => {
                return Err(CodeDiagnostic::FunctionOrStaticExpectedHere)
                    .with_span_from(&self.scope, node);
            }
        };

        let result = ExprKind::Fn(fn_kind, Some(arguments));
        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_type_cast_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;
        let ty = TypeVisitor::new(
            self.global_ctx.clone(),
            self.ast,
            self.scope.clone(),
            self.macro_ctx,
        )
        .visit(node.child_by_field(FieldKind::Type).unwrap())?;

        Ok(ExprKind::Cast(value, ty).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_loop_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let body = self.visit(node.child_by_field(FieldKind::Body).unwrap())?;
        Ok(ExprKind::Loop(body).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_break_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = node
            .child_by_field(FieldKind::Inner)
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(ExprKind::Break(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_return_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = node
            .child_by_field(FieldKind::Inner)
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(ExprKind::Return(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_yield_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = node
            .child_by_field(FieldKind::Inner)
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(ExprKind::Yield(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_defer_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;

        Ok(ExprKind::Defer(inner).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_continue_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(ExprKind::Continue.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_static_for_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let range = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;

        let body;
        let loop_var;
        if let Some(name_node) = node.child_by_field(FieldKind::Name) {
            let name = self.code.node_text(name_node).alloc_on(self.ast);
            let id = self.ast.make_id();

            body = with_block_scope!(self, {
                self.ast.add_local_name(id, name);
                self.scope
                    .add_item(
                        Some(name),
                        NamedItem::new_default(NamedItemKind::ConstLocal(id), name_node, None),
                    )
                    .with_span_from(&self.scope, node)?;

                self.visit(node.child_by_field(FieldKind::Body).unwrap())?
            });
            loop_var = StaticForLoopVariable::Single(id);
        } else {
            body = with_block_scope!(self, {
                let mut cursor = node.walk();
                let mut loop_vars = vec![];

                for name_node in node.children_by_field(FieldKind::Element, &mut cursor) {
                    let name = self.code.node_text(name_node).alloc_on(self.ast);
                    let elem_id = self.ast.make_id();

                    loop_vars.push(elem_id);
                    self.ast.add_local_name(elem_id, name);
                    self.scope
                        .add_item(
                            Some(name),
                            NamedItem::new_default(
                                NamedItemKind::ConstLocal(elem_id),
                                name_node,
                                None,
                            ),
                        )
                        .with_span_from(&self.scope, name_node)?;
                }

                loop_var = StaticForLoopVariable::Tuple(loop_vars.alloc_on(self.ast));
                self.visit(node.child_by_field(FieldKind::Body).unwrap())?
            });
        };

        let result = ExprKind::StaticFor(loop_var, range, body);
        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_for_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let iterable_node = node.child_by_field(FieldKind::Value).unwrap();
        let iterable = self.visit(iterable_node)?;

        let iterator = self.ast.make_id();
        let iterator_result = self.ast.make_id();

        let id = self.ast.make_id();

        let body = if let Some(name_node) = node.child_by_field(FieldKind::Name) {
            let name = self.code.node_text(name_node).alloc_on(self.ast);

            with_block_scope!(self, {
                self.ast.add_local_name(id, name);
                self.scope
                    .add_item(
                        Some(name),
                        NamedItem::new_default(NamedItemKind::Local(id), name_node, None),
                    )
                    .with_span_from(&self.scope, node)?;

                self.visit(node.child_by_field(FieldKind::Body).unwrap())?
            })
        } else {
            // Tuple unpacking, i.e. `for (a, b) in ...`
            with_block_scope!(self, {
                let mut statements = Vec::new();
                let mut cursor = node.walk();

                for (idx, name_node) in node
                    .children_by_field(FieldKind::Element, &mut cursor)
                    .enumerate()
                {
                    let name = self.code.node_text(name_node).alloc_on(self.ast);
                    let elem_id = self.ast.make_id();

                    let rhs = ExprKind::TupleIndex(
                        ExprKind::Local(id).alloc_with_span_from(self.ast, &self.scope, name_node),
                        ExprKind::Lit(Lit::Int(false, idx as u128, None)).alloc_with_span_from(
                            self.ast,
                            &self.scope,
                            name_node,
                        ),
                    )
                    .alloc_with_span_from(self.ast, &self.scope, name_node);

                    let elem_decl = LetDeclaration {
                        id: elem_id,
                        ty: None,
                        value: Some(rhs),
                    };

                    statements.push(
                        StatementKind::LetDeclaration(elem_decl).alloc_with_span_from(
                            self.ast,
                            &self.scope,
                            node,
                        ),
                    );
                    self.ast.add_local_name(elem_id, name);
                    self.scope
                        .add_item(
                            Some(name),
                            NamedItem::new_default(NamedItemKind::Local(elem_id), name_node, None),
                        )
                        .with_span_from(&self.scope, name_node)?;
                }

                let ret = self.visit(node.child_by_field(FieldKind::Body).unwrap())?;

                ExprKind::Block(statements.alloc_on(self.ast), ret).alloc_with_span_from(
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
                kind: NamedItemKind::Function(item),
                ..
            })) => Some(item),
            _ => None,
        };

        let loop_if = ExprKind::If(
            ExprKind::Field(
                ExprKind::Local(iterator_result).alloc_with_span(self.ast, None),
                "_is_some",
                None,
                None,
            )
            .alloc_with_span(self.ast, None),
            ExprKind::Block(
                vec![StatementKind::LetDeclaration(LetDeclaration {
                    id,
                    ty: None,
                    value: Some(
                        ExprKind::Field(
                            ExprKind::Local(iterator_result).alloc_with_span(self.ast, None),
                            "_inner",
                            None,
                            None,
                        )
                        .alloc_with_span(self.ast, None),
                    ),
                })
                .alloc_with_span(self.ast, None)]
                .alloc_on(self.ast),
                body,
            )
            .alloc_with_span(self.ast, None),
            ExprKind::Break(None).alloc_with_span(self.ast, None),
        );

        let loop_body = ExprKind::Loop(
            ExprKind::Block(
                vec![StatementKind::LetDeclaration(LetDeclaration {
                    id: iterator_result,
                    ty: None,
                    value: Some(
                        ExprKind::Call(
                            ExprKind::Field(
                                ExprKind::Local(iterator).alloc_with_span(self.ast, None),
                                "next",
                                None,
                                None,
                            )
                            .alloc_with_span(self.ast, None),
                            vec![].alloc_on(self.ast),
                        )
                        .alloc_with_span(self.ast, None),
                    ),
                })
                .alloc_with_span(self.ast, None)]
                .alloc_on(self.ast),
                loop_if.alloc_with_span(self.ast, None),
            )
            .alloc_with_span_from(self.ast, &self.scope, node),
        );

        let result = ExprKind::Block(
            vec![StatementKind::LetDeclaration(LetDeclaration {
                id: iterator,
                ty: None,
                value: Some(
                    ExprKind::Call(
                        ExprKind::Field(iterable, "iter", unified_fn, None).alloc_with_span_from(
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
            loop_body.alloc_with_span(self.ast, None),
        );

        Ok(result.alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_switch_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;

        let mut arms = Vec::new();
        let mut default_arm = None;

        let body = node.child_by_field(FieldKind::Body).unwrap();
        let mut cursor = body.walk();

        // Switch is desugared into a series of if-else expressions
        for arm in body.children_by_field(FieldKind::Arm, &mut cursor) {
            if default_arm.is_some() {
                return Err(CodeDiagnostic::DefaultCaseMustBeLast).with_span_from(&self.scope, arm);
            }

            let pattern = arm.child_by_field(FieldKind::Pattern).unwrap();
            let mut cursor = pattern.walk();

            let alternatives = pattern
                .children_by_field(FieldKind::Value, &mut cursor)
                .map(|child| self.visit(child))
                .collect::<Result<Vec<_>, _>>()?;

            if !alternatives.is_empty() {
                arms.push((
                    arm,
                    alternatives,
                    self.visit(arm.child_by_field(FieldKind::Value).unwrap())?,
                ))
            } else {
                default_arm = Some(self.visit(arm.child_by_field(FieldKind::Value).unwrap())?);
            }
        }

        let local_id = self.ast.make_id();
        let local = ExprKind::Local(local_id).alloc_with_span_from(self.ast, &self.scope, node);
        let stmts = vec![StatementKind::LetDeclaration(LetDeclaration {
            id: local_id,
            ty: None,
            value: Some(value),
        })
        .alloc_with_span(self.ast, None)];

        let ret = arms.into_iter().rfold(
            default_arm.unwrap_or_else(|| ExprKind::Void.alloc_with_span(self.ast, None)),
            |acc, (_arm_node, alternatives, value)| {
                // TODO: add spans here
                let cmp = alternatives
                    .into_iter()
                    .fold(None, |acc, alternative| match acc {
                        Some(acc) => Some(
                            ExprKind::Binary(
                                BinOp::Or,
                                acc,
                                ExprKind::Binary(BinOp::Eq, local, alternative)
                                    .alloc_with_span(self.ast, None),
                            )
                            .alloc_with_span(self.ast, None),
                        ),
                        None => Some(
                            ExprKind::Binary(BinOp::Eq, local, alternative)
                                .alloc_with_span(self.ast, None),
                        ),
                    })
                    .unwrap();
                let branch = ExprKind::If(cmp, value, acc);

                branch.alloc_with_span(self.ast, None)
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
        let ty = TypeVisitor::new(
            self.global_ctx.clone(),
            self.ast,
            self.scope.clone(),
            self.macro_ctx,
        )
        .visit(node.child_by_field(FieldKind::Name).unwrap())?;

        let initializer_node = node.child_by_field(FieldKind::Arguments).unwrap();
        let mut field_initializers = Vec::new();
        let mut names = HashSet::default();

        with_block_scope!(self, {
            let mut cursor = initializer_node.walk();

            for node in initializer_node.children_by_field(FieldKind::Item, &mut cursor) {
                let name = self
                    .code
                    .node_text(node.child_by_field(FieldKind::Field).unwrap());

                if !names.insert(name) {
                    return Err(CodeDiagnostic::DuplicateFieldInitializer(name.to_string()))
                        .with_span_from(&self.scope, node);
                }

                let value = self.visit(node.child_by_field(FieldKind::Value).unwrap())?;

                let span = Span::from_node(self.scope.code().unwrap().file_id(), node);

                field_initializers.push(FieldInitializer {
                    name: name.alloc_on(self.ast),
                    value,
                    span: Some(span),
                });
            }
        });

        Ok(
            ExprKind::Struct(ty, field_initializers.alloc_on(self.ast)).alloc_with_span_from(
                self.ast,
                &self.scope,
                node,
            ),
        )
    }

    fn visit_while_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let condition = self.visit(node.child_by_field(FieldKind::Condition).unwrap())?;
        let body = self.visit(node.child_by_field(FieldKind::Body).unwrap())?;

        let r#break = ExprKind::Break(None).alloc_with_span_from(self.ast, &self.scope, node);
        let condition =
            ExprKind::Tag("loop_condition", condition).alloc_with_span(self.ast, condition.span);

        let body = ExprKind::If(condition, body, r#break).alloc_with_span_from(
            self.ast,
            &self.scope,
            node,
        );

        Ok(ExprKind::Loop(body).alloc_with_span_from(self.ast, &self.scope, node))
    }

    fn visit_et_cetera_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if node.child_by_field(FieldKind::Macro).is_some() {
            if !self.macro_ctx.in_a_macro {
                return Err(CodeDiagnostic::MacroEtCeteraOutsideOfMacro)
                    .with_span_from(&self.scope, node);
            }

            if !self.macro_ctx.has_et_cetera {
                return Err(CodeDiagnostic::NoMacroEtCeteraArgs).with_span_from(&self.scope, node);
            }

            let inner = self.visit(node.child_by_field(FieldKind::Inner).unwrap())?;
            Ok(ExprKind::EtCeteraMacro(inner).alloc_with_span_from(self.ast, &self.scope, node))
        } else {
            Err(CodeDiagnostic::EtCeteraExprInUnsupported).with_span_from(&self.scope, node)
        }
    }

    fn visit_macro_invocation(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let expr = self.visit(node.child_by_field(FieldKind::Macro).unwrap())?;

        let span = Span::from_node(self.scope.file_id(), node);
        let mut args = Vec::new();
        let arguments_node = node.child_by_field(FieldKind::Arguments).unwrap();
        let mut cursor = arguments_node.walk();
        for node in arguments_node.children_by_field(FieldKind::Inner, &mut cursor) {
            args.push(self.visit(node)?);
        }

        if self.macro_ctx.in_a_macro {
            Ok(ExprKind::MacroInvocation(expr, args.alloc_on(self.ast))
                .alloc_with_span(self.ast, Some(span)))
        } else {
            let r#macro = match expr.kind {
                ExprKind::Macro(item, bound_params) => {
                    args = bound_params.iter().copied().chain(args).collect();
                    item
                }
                _ => return Err(CodeDiagnostic::NotAMacro).with_span_from(&self.scope, node),
            };

            let expander =
                MacroExpander::new(self.ast, self.global_ctx.clone(), Some(span), r#macro, args);
            expander.expand()
        }
    }

    fn visit_universal_macro_invocation(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.macro_ctx);
        let path = visitor.visit(node.child_by_field(FieldKind::Macro).unwrap())?;

        let span = Span::from_node(self.scope.file_id(), node);

        let mut arguments = Vec::new();
        arguments.push(self.visit(node.child_by_field(FieldKind::Value).unwrap())?);

        let arguments_node = node.child_by_field(FieldKind::Arguments).unwrap();
        let mut cursor = arguments_node.walk();

        for node in arguments_node.children_by_field(FieldKind::Inner, &mut cursor) {
            arguments.push(self.visit(node)?);
        }
        self.visit_macro_invocation_impl(path, arguments, span)
    }
}

pub fn parse_string_literal(lit: &str) -> Result<Vec<u8>, CodeDiagnostic> {
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
                    return Err(CodeDiagnostic::InvalidEscapeSequence);
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
                    let ch = u32::from_str_radix(&buf, 16)
                        .map_err(|_| CodeDiagnostic::InvalidEscapeSequence)?;

                    let utf8 = char::from_u32(ch)
                        .ok_or(CodeDiagnostic::InvalidEscapeSequence)?
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
                    let ch = u32::from_str_radix(&buf, 16)
                        .map_err(|_| CodeDiagnostic::InvalidEscapeSequence)?;
                    let utf8 = char::from_u32(ch)
                        .ok_or(CodeDiagnostic::InvalidEscapeSequence)?
                        .to_string();
                    result.extend(utf8.as_bytes());
                    buf.clear();
                    State::Normal
                }
                _ => {
                    buf.push(ch as char);
                    State::UnicodeLong
                }
            },
        };
    }

    match state {
        State::Normal => Ok(result),
        _ => Err(CodeDiagnostic::InvalidEscapeSequence),
    }
}

pub struct LambdaVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    self_param: Id,

    parameters: Vec<Parameter<'ast>>,
    bound_values: IndexMap<Id, (BoundItemType, &'ast str, ExprP<'ast>)>,
    placeholders: Vec<Placeholder<'ast>>,
    return_type: Option<TyP<'ast>>,
    body: Option<ExprP<'ast>>,
    macro_ctx: MacroCtx,
}

impl<'ast, 'src> LambdaVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        global_ctx: GlobalCtx,
        scope: Scope<'ast, 'src>,
        macro_ctx: MacroCtx,
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
            bound_values: IndexMap::default(),
            return_type: None,
            body: None,
            macro_ctx,
        }
    }

    pub fn generate(
        mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<(ItemP<'ast>, &'ast [ClosureBinding<'ast>]), AluminaError> {
        self.visit(node)?;

        let item = self.ast.make_item();
        let span = Span::from_node(self.scope.file_id(), node);

        if !self.bound_values.is_empty() {
            let placeholder = self.ast.make_id();
            self.placeholders.push(Placeholder {
                id: placeholder,
                bounds: super::ProtocolBounds {
                    kind: super::ProtocolBoundsKind::All,
                    bounds: &[],
                },
                span: None,
                default: None,
            });

            let span = Span::from_node(self.scope.file_id(), node);

            // Closure struct is passed by a mutable pointer
            let placeholder_ty = self.ast.intern_type(Ty::Placeholder(placeholder));
            self.parameters.insert(
                0,
                Parameter {
                    id: self.self_param,
                    ty: self.ast.intern_type(Ty::Pointer(placeholder_ty, false)),
                    span: Some(span),
                },
            );
        }

        self.scope.check_unused_items(&self.global_ctx.diag());

        item.assign(Item::Function(Function {
            name: None,
            attributes: [].alloc_on(self.ast),
            placeholders: self.placeholders.alloc_on(self.ast),
            args: self.parameters.alloc_on(self.ast),
            return_type: self.return_type.unwrap(),
            body: Some(self.body.unwrap()),
            varargs: false,
            span: Some(span),
            is_local: true,
            is_lambda: true,
            is_protocol_fn: false,
        }));

        let bindings = self
            .bound_values
            .into_iter()
            .map(|(id, (binding_type, name, value))| super::ClosureBinding {
                id,
                value,
                name,
                binding_type,
                span: value.span,
            })
            .collect::<Vec<_>>()
            .alloc_on(self.ast);

        Ok((item, bindings))
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for LambdaVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_parameter(&mut self, node: tree_sitter::Node<'src>) -> Result<(), AluminaError> {
        let name_node = node.child_by_field(FieldKind::Name).unwrap();
        let name = self.code.node_text(name_node).alloc_on(self.ast);
        let id = self.ast.make_id();

        self.ast.add_local_name(id, name);
        self.scope
            .add_item(
                Some(name),
                NamedItem::new_default(NamedItemKind::Parameter(id), node, None),
            )
            .with_span_from(&self.scope, node)?;

        let field_type = TypeVisitor::new(
            self.global_ctx.clone(),
            self.ast,
            self.scope.clone(),
            self.macro_ctx,
        )
        .visit(node.child_by_field(FieldKind::Type).unwrap())?;

        let span = Span::from_node(self.scope.file_id(), node);

        self.parameters.push(Parameter {
            id,
            ty: field_type,
            span: Some(span),
        });

        Ok(())
    }

    fn visit_bound_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self
            .code
            .node_text(node.child_by_field(FieldKind::Name).unwrap())
            .alloc_on(self.ast)
            .trim_start_matches('@');

        let bound_type = if node.child_by_field(FieldKind::ByReference).is_some() {
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
                kind:
                    NamedItemKind::Local(id)
                    | NamedItemKind::Parameter(id)
                    | NamedItemKind::ConstLocal(id),
                ..
            }) => ExprKind::Local(id),
            ItemResolution::Item(NamedItem {
                kind: NamedItemKind::BoundValue(self_arg, id, bound_type),
                ..
            }) => ExprKind::BoundParam(self_arg, id, bound_type),
            _ => {
                return Err(CodeDiagnostic::CanOnlyCloseOverLocals)
                    .with_span_from(&self.scope, node)
            }
        };

        let id = self.ast.make_id();
        self.ast.add_local_name(id, name);
        self.scope
            .add_item(
                Some(name),
                NamedItem::new_default(
                    NamedItemKind::BoundValue(self.self_param, id, bound_type),
                    node,
                    None,
                ),
            )
            .with_span_from(&self.scope, node)?;

        self.bound_values.insert(
            id,
            (
                bound_type,
                name,
                original.alloc_with_span_from(self.ast, &self.scope, node),
            ),
        );

        Ok(())
    }

    fn visit_closure_parameters(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();

        for param in node.children_by_field(FieldKind::Parameter, &mut cursor) {
            self.visit(param)?
        }

        Ok(())
    }

    fn visit_lambda_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit(node.child_by_field(FieldKind::Parameters).unwrap())?;

        self.body = Some(
            ExpressionVisitor::new(
                self.ast,
                self.global_ctx.clone(),
                self.scope.clone(),
                self.macro_ctx,
            )
            .generate(node.child_by_field(FieldKind::Body).unwrap())?,
        );

        self.return_type = Some(
            node.child_by_field(FieldKind::ReturnType)
                .map(|node| {
                    TypeVisitor::new(
                        self.global_ctx.clone(),
                        self.ast,
                        self.scope.clone(),
                        self.macro_ctx,
                    )
                    .visit(node)
                })
                .transpose()?
                .unwrap_or_else(|| self.ast.intern_type(Ty::void())),
        );

        Ok(())
    }
}

#[allow(clippy::needless_lifetimes)]
pub fn resolve_name<'ast, 'src>(
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    scope: &Scope<'ast, 'src>,
    path: Path<'ast>,
    span: Option<Span>,
) -> Result<ExprP<'ast>, AluminaError> {
    let mut resolver = NameResolver::new();
    let expr = match resolver
        .resolve_item(scope.clone(), path.clone())
        .with_span(span)?
    {
        ItemResolution::Item(named_item) => match named_item.kind {
            NamedItemKind::Function(fun) => ExprKind::Fn(FnKind::Normal(fun), None),
            NamedItemKind::Method(fun) => ExprKind::Fn(FnKind::Normal(fun), None),
            NamedItemKind::Local(var) => ExprKind::Local(var),
            NamedItemKind::ConstLocal(var) => ExprKind::Local(var),
            NamedItemKind::BoundValue(self_id, var, bound_type) => {
                ExprKind::BoundParam(self_id, var, bound_type)
            }
            NamedItemKind::MacroParameter(var, _) => ExprKind::Local(var),
            NamedItemKind::Parameter(var) => ExprKind::Local(var),
            NamedItemKind::Static(var) => ExprKind::Static(var, None),
            NamedItemKind::Const(var) => ExprKind::Const(var, None),
            //NamedItemKind::EnumMember(typ, var, _) => ExprKind::EnumValue(typ, var),
            NamedItemKind::Macro(item) => {
                if let (Some(node), Some(ref scope)) = (named_item.node, named_item.scope) {
                    let mut macro_maker = MacroMaker::new(ast, global_ctx);
                    macro_maker.make(
                        Some(path.segments.last().unwrap().0),
                        item,
                        node,
                        scope.clone(),
                        named_item.attributes,
                    )?;
                }

                ExprKind::Macro(item, &[])
            }
            kind => return Err(CodeDiagnostic::Unexpected(format!("{}", kind))).with_span(span),
        },
        ItemResolution::Defered(ty, name) => {
            let name = name.0.alloc_on(ast);
            let ty = ast.intern_type(ty);
            ExprKind::Defered(Defered { ty, name })
        }
    };

    Ok(expr.alloc_with_span(ast, span))
}
