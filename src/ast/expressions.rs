use std::collections::HashSet;

use crate::ast::{AstCtx, FieldInitializer};
use crate::ast::{BinOp, Expr, ExprP, LetDeclaration, Lit, Statement, UnOp};
use crate::common::AluminaErrorKind;
use crate::common::ArenaAllocatable;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::resolver::ItemResolution;
use crate::name_resolution::scope::ScopeType;
use crate::parser::ParseCtx;
use crate::visitors::ScopedPathVisitor;
use crate::visitors::UseClauseVisitor;
use crate::AluminaVisitor;
use crate::{
    common::{SyntaxError, ToSyntaxError},
    name_resolution::{
        resolver::NameResolver,
        scope::{NamedItem, Scope},
    },
};

use super::types::TypeVisitor;
use super::{AstId, BuiltinType, DeferredFn, FnKind, Function, Item, ItemP, Parameter, Ty, TyP};

macro_rules! with_block_scope {
    ($self:ident, $body:expr) => {{
        let child_scope = $self.scope.anonymous_child(ScopeType::Block);
        let previous_scope = std::mem::replace(&mut $self.scope, child_scope);
        let result = $body;
        $self.scope = previous_scope;
        result
    }};
}

pub struct ExpressionVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    in_a_loop: bool,

    additional_items: Vec<ItemP<'ast>>,
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
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        ExpressionVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            in_a_loop: false,
            additional_items: Vec::new(),
        }
    }

    pub fn generate(
        mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<(ExprP<'ast>, Vec<ItemP<'ast>>), SyntaxError> {
        let result = self.visit(node)?;
        Ok((result, self.additional_items))
    }

    fn visit_ref(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<ExprP<'ast>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let expr = match resolver
            .resolve_item(self.scope.clone(), path)
            .to_syntax_error(node)?
        {
            ItemResolution::Item(NamedItem::Function(fun, _, _)) => {
                Expr::Fn(FnKind::Normal(fun), None)
            }
            ItemResolution::Item(NamedItem::Local(var)) => Expr::Local(var),
            ItemResolution::Item(NamedItem::Parameter(var, _)) => Expr::Local(var),
            ItemResolution::Item(NamedItem::EnumMember(typ, var, _)) => Expr::EnumValue(typ, var),
            ItemResolution::Defered(placeholder, name) => {
                let name = name.0.alloc_on(self.ast);
                Expr::Fn(FnKind::Defered(DeferredFn { placeholder, name }), None)
            }
            a => panic!("{:?} at {:?}", a, node),
        };

        Ok(expr.alloc_on(self.ast))
    }

    fn visit_statement(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<Option<Statement<'ast>>, SyntaxError<'src>> {
        let inner = node.child_by_field_name("inner").unwrap();
        let result = match inner.kind() {
            "empty_statement" => None,
            "let_declaration" => {
                let name = self
                    .code
                    .node_text(inner.child_by_field_name("name").unwrap())
                    .alloc_on(self.ast);

                let id = self.ast.make_id();
                let typ = inner
                    .child_by_field_name("type")
                    .map(|n| TypeVisitor::new(self.ast, self.scope.clone()).visit(n))
                    .transpose()?;

                // We need to visit the init expression before we add the name to the scope to ensure
                // we cannot refer to ourselves during init.
                let value = inner
                    .child_by_field_name("value")
                    .map(|n| self.visit(n))
                    .transpose()?;

                self.scope
                    .add_item(name, NamedItem::Local(id))
                    .to_syntax_error(inner)?;

                let let_decl = LetDeclaration { id, typ, value };

                Some(Statement::LetDeclaration(let_decl))
            }
            "use_declaration" => {
                UseClauseVisitor::new(self.ast, self.scope.clone())
                    .visit(inner.child_by_field_name("argument").unwrap())?;
                None
            }
            "expression_statement" => Some(Statement::Expression(
                self.visit(inner.child_by_field_name("inner").unwrap())?,
            )),
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
            None => return Expr::Void.alloc_on(self.ast),
        };

        let expression_node = match last_node.kind() {
            "expression_statement" => last_node.child_by_field_name("inner").unwrap(),
            _ => return Expr::Void.alloc_on(self.ast),
        };

        match expression_node.kind() {
            "block" | "if_expression" | "switch_expression" | "while_expression"
            | "loop_expression" | "for_expression" => match statements.pop() {
                Some(Statement::Expression(expr)) => expr,
                _ => unreachable!(),
            },
            _ => Expr::Void.alloc_on(self.ast),
        }
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for ExpressionVisitor<'ast, 'src> {
    type ReturnType = Result<ExprP<'ast>, SyntaxError<'src>>;

    fn visit_block(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let mut statements = Vec::new();

        let return_expression = with_block_scope!(self, {
            let mut last_node = None;
            for node in node.children_by_field_name("statements", &mut cursor) {
                last_node = Some(node.child_by_field_name("inner").unwrap());
                if let Some(stmt) = self.visit_statement(node)? {
                    statements.push(stmt);
                }
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
            Expr::Block(statements, return_expression).alloc_on(self.ast)
        };

        Ok(result)
    }

    fn visit_closure_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (func, additional_items) =
            ClosureVisitor::new(self.ast, self.scope.anonymous_child(ScopeType::Closure))
                .generate(node)?;

        self.additional_items.extend(additional_items);
        self.additional_items.push(func);

        Ok(Expr::Fn(FnKind::Normal(func), None).alloc_on(self.ast))
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

        let value = remainder
            .parse()
            .map_err(|_| AluminaErrorKind::InvalidLiteral)
            .to_syntax_error(node)?;

        Ok(Expr::Lit(Lit::Int(value, kind)).alloc_on(self.ast))
    }

    fn visit_float_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (remainder, kind) = suffixed_literals!(self.code.node_text(node),
            "f32" => BuiltinType::U8,
            "f64" => BuiltinType::U16,
        );

        Ok(Expr::Lit(Lit::Float(remainder.alloc_on(self.ast), kind)).alloc_on(self.ast))
    }

    fn visit_string_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let s = parse_string_literal(self.code.node_text(node))
            .to_syntax_error(node)?
            .as_str()
            .alloc_on(self.ast);

        let s = self.ast.arena.alloc_slice_copy(s.as_bytes());
        Ok(Expr::Lit(Lit::Str(s)).alloc_on(self.ast))
    }

    fn visit_boolean_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self
            .code
            .node_text(node)
            .parse()
            .map_err(|_| AluminaErrorKind::InvalidLiteral)
            .to_syntax_error(node)?;

        Ok(Expr::Lit(Lit::Bool(value)).alloc_on(self.ast))
    }

    fn visit_ptr_literal(&mut self, _node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(Expr::Lit(Lit::Null).alloc_on(self.ast))
    }

    fn visit_void_literal(&mut self, _node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(Expr::Void.alloc_on(self.ast))
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

        Ok(Expr::Binary(op, lhs, rhs).alloc_on(self.ast))
    }

    fn visit_assignment_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field_name("left").unwrap())?;
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;

        Ok(Expr::Assign(lhs, rhs).alloc_on(self.ast))
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
        let result = Expr::AssignOp(op, lhs, rhs);

        Ok(result.alloc_on(self.ast))
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
        let result = Expr::Call(func, arguments);

        Ok(result.alloc_on(self.ast))
    }

    fn visit_tuple_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field_name("element", &mut cursor) {
            elements.push(self.visit(node)?);
        }

        let result = match elements[..] {
            [] => Expr::Void.alloc_on(self.ast),
            [e] => e,
            _ => {
                let elements = elements.alloc_on(self.ast);
                Expr::Tuple(elements).alloc_on(self.ast)
            }
        };

        Ok(result)
    }

    fn visit_array_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field_name("element", &mut cursor) {
            elements.push(self.visit(node)?);
        }

        let elements = elements.alloc_on(self.ast);
        let result = Expr::Array(elements).alloc_on(self.ast);

        Ok(result)
    }

    fn visit_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
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
        Ok(Expr::Unary(op, value).alloc_on(self.ast))
    }

    fn visit_reference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(Expr::Ref(value).alloc_on(self.ast))
    }

    fn visit_dereference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(Expr::Deref(value).alloc_on(self.ast))
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
                    Ok(ItemResolution::Item(NamedItem::Function(item, _, _))) => Some(item),
                    _ => None,
                };

                Expr::Field(value, field_value.alloc_on(self.ast), unified_fn)
            }
            "integer_literal" => Expr::TupleIndex(value, field_value.parse().unwrap()),
            _ => unreachable!(),
        };

        Ok(result.alloc_on(self.ast))
    }

    fn visit_index_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;

        let result;
        if let Some(index) = node.child_by_field_name("index") {
            let index = self.visit(index)?;
            result = Expr::Index(value, index);
        } else if let Some(range) = node.child_by_field_name("range") {
            let lower_bound = range
                .child_by_field_name("lower")
                .map(|n| self.visit(n))
                .transpose()?;
            let upper_bound = range
                .child_by_field_name("upper")
                .map(|n| self.visit(n))
                .transpose()?;

            result = Expr::RangeIndex(value, lower_bound, upper_bound);
        } else {
            unreachable!();
        }

        Ok(result.alloc_on(self.ast))
    }

    fn visit_if_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let condition = self.visit(node.child_by_field_name("condition").unwrap())?;
        let consequence = self.visit(node.child_by_field_name("consequence").unwrap())?;
        let alternative = match node.child_by_field_name("alternative") {
            Some(node) => self.visit(node)?,
            None => Expr::Void.alloc_on(self.ast),
        };

        let result = Expr::If(condition, consequence, alternative);
        Ok(result.alloc_on(self.ast))
    }

    fn visit_generic_function(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let fn_kind = match self.visit(node.child_by_field_name("function").unwrap())? {
            Expr::Fn(fn_kind, None) => fn_kind.clone(),
            _ => return Err(AluminaErrorKind::FunctionExpectedHere).to_syntax_error(node),
        };

        let mut type_visitor = TypeVisitor::new(self.ast, self.scope.clone());

        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| type_visitor.visit(child))
            .collect::<Result<Vec<_>, _>>()?
            .alloc_on(self.ast);

        let result = Expr::Fn(fn_kind, Some(arguments));
        Ok(result.alloc_on(self.ast))
    }

    fn visit_type_cast_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        let typ = TypeVisitor::new(self.ast, self.scope.clone())
            .visit(node.child_by_field_name("type").unwrap())?;

        Ok(Expr::Cast(value, typ).alloc_on(self.ast))
    }

    fn visit_loop_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.in_a_loop = true;
        let body = self.visit(node.child_by_field_name("body").unwrap());
        self.in_a_loop = false;
        let body = body?;

        Ok(Expr::Loop(body).alloc_on(self.ast))
    }

    fn visit_break_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_loop {
            return Err(AluminaErrorKind::BreakOutsideOfLoop).to_syntax_error(node);
        }

        let inner = node
            .child_by_field_name("inner")
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(Expr::Break(inner).alloc_on(self.ast))
    }

    fn visit_return_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let inner = node
            .child_by_field_name("inner")
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(Expr::Return(inner).alloc_on(self.ast))
    }

    fn visit_continue_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_loop {
            return Err(AluminaErrorKind::ContinueOutsideOfLoop).to_syntax_error(node);
        }
        Ok(Expr::Continue.alloc_on(self.ast))
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
                return Err(AluminaErrorKind::DefaultCaseMustBeLast).to_syntax_error(arm);
            }

            let pattern = arm.child_by_field_name("pattern").unwrap();
            if let Some(expr) = pattern.child_by_field_name("value") {
                arms.push((
                    self.visit(expr)?,
                    self.visit(arm.child_by_field_name("value").unwrap())?,
                ))
            } else {
                default_arm = Some(self.visit(arm.child_by_field_name("value").unwrap())?);
            }
        }

        let local_id = self.ast.make_id();
        let local = Expr::Local(local_id).alloc_on(self.ast);
        let stmts = vec![Statement::LetDeclaration(LetDeclaration {
            id: local_id,
            typ: None,
            value: Some(value),
        })];

        let ret = arms.into_iter().rfold(
            default_arm.unwrap_or(Expr::Void.alloc_on(self.ast)),
            |acc, (pattern, value)| {
                let cmp = Expr::Binary(BinOp::Eq, local, pattern);
                let branch = Expr::If(cmp.alloc_on(self.ast), value, acc);

                branch.alloc_on(self.ast)
            },
        );

        let block = Expr::Block(stmts.alloc_on(self.ast), ret).alloc_on(self.ast);

        Ok(block.alloc_on(self.ast))
    }

    fn visit_struct_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let typ = TypeVisitor::new(self.ast, self.scope.clone())
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
                    return Err(AluminaErrorKind::DuplicateFieldInitializer(
                        name.to_string(),
                    ))
                    .to_syntax_error(node);
                }

                let value = self.visit(node.child_by_field_name("value").unwrap())?;

                field_initializers.push(FieldInitializer {
                    name: name.alloc_on(self.ast),
                    value,
                });
            }
        });

        Ok(Expr::Struct(typ, field_initializers.alloc_on(self.ast)).alloc_on(self.ast))
    }

    fn visit_while_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let condition = self.visit(node.child_by_field_name("condition").unwrap())?;

        self.in_a_loop = true;
        let body = self.visit(node.child_by_field_name("body").unwrap());
        self.in_a_loop = false;
        let body = body?;

        let r#break = Expr::Break(None).alloc_on(self.ast);
        let body = Expr::If(condition, body, r#break).alloc_on(self.ast);

        Ok(Expr::Loop(body).alloc_on(self.ast))
    }
}

fn parse_string_literal(lit: &str) -> Result<String, AluminaErrorKind> {
    let mut result = String::with_capacity(lit.len());

    enum State {
        Normal,
        Escape,
        Hex,
        UnicodeStart,
        UnicodeShort,
        UnicodeLong,
    };

    let mut state = State::Normal;
    let mut buf = String::with_capacity(4);

    for ch in lit[1..lit.len() - 1].chars() {
        state = match state {
            State::Normal => match ch {
                '\\' => State::Escape,
                _ => {
                    result.push(ch);
                    State::Normal
                }
            },
            State::Escape => match ch {
                '\\' => {
                    result.push('\\');
                    State::Normal
                }
                'n' => {
                    result.push('\n');
                    State::Normal
                }
                'r' => {
                    result.push('\r');
                    State::Normal
                }
                't' => {
                    result.push('\t');
                    State::Normal
                }
                '\'' => {
                    result.push('\'');
                    State::Normal
                }
                '"' => {
                    result.push('"');
                    State::Normal
                }
                'x' => State::Hex,
                'u' => State::UnicodeStart,
                _ => {
                    return Err(AluminaErrorKind::InvalidEscapeSequence);
                }
            },
            State::Hex => {
                if buf.len() == 2 {
                    let ch = u8::from_str_radix(&buf, 16).unwrap();
                    result.push(ch as char);
                    buf.clear();
                    State::Normal
                } else {
                    buf.push(ch);
                    State::Hex
                }
            }
            State::UnicodeStart => match ch {
                '{' => State::UnicodeLong,
                _ => {
                    buf.push(ch);
                    State::UnicodeShort
                }
            },
            State::UnicodeShort => {
                if buf.len() == 4 {
                    let ch = u32::from_str_radix(&buf, 16).unwrap();
                    result.push(
                        ch.try_into()
                            .map_err(|_| AluminaErrorKind::InvalidEscapeSequence)?,
                    );
                    buf.clear();
                    State::Normal
                } else {
                    buf.push(ch);
                    State::UnicodeShort
                }
            }
            State::UnicodeLong => match ch {
                '}' => {
                    let ch = u32::from_str_radix(&buf, 16).unwrap();
                    result.push(
                        ch.try_into()
                            .map_err(|_| AluminaErrorKind::InvalidEscapeSequence)?,
                    );
                    buf.clear();
                    State::Normal
                }
                _ => {
                    buf.push(ch);
                    State::UnicodeShort
                }
            },
        };
    }

    match state {
        State::Normal => Ok(result),
        _ => Err(AluminaErrorKind::InvalidEscapeSequence),
    }
}

pub struct ClosureVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    additional_items: Vec<ItemP<'ast>>,

    parameters: Vec<Parameter<'ast>>,
    placeholders: Vec<AstId>,
    return_type: Option<TyP<'ast>>,
    body: Option<ExprP<'ast>>,
}

impl<'ast, 'src> ClosureVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        Self {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            additional_items: Vec::new(),
            parameters: Vec::new(),
            placeholders: Vec::new(),
            return_type: None,
            body: None,
        }
    }

    pub fn generate(
        mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<(ItemP<'ast>, Vec<ItemP<'ast>>), SyntaxError<'src>> {
        self.visit(node)?;

        let symbol = self.ast.make_symbol();
        symbol.assign(Item::Function(Function {
            name: None,
            attributes: [].alloc_on(self.ast),
            placeholders: self.placeholders.alloc_on(self.ast),
            args: self.parameters.alloc_on(self.ast),
            return_type: self.return_type.unwrap(),
            body: Some(self.body.unwrap()),
        }));

        Ok((symbol, self.additional_items))
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for ClosureVisitor<'ast, 'src> {
    type ReturnType = Result<(), SyntaxError<'src>>;

    fn visit_parameter(&mut self, node: tree_sitter::Node<'src>) -> Result<(), SyntaxError<'src>> {
        let name_node = node.child_by_field_name("name").unwrap();
        let name = self.code.node_text(name_node).alloc_on(self.ast);
        let id = self.ast.make_id();

        self.scope
            .add_item(name, NamedItem::Parameter(id, node))
            .to_syntax_error(node)?;

        let field_type = TypeVisitor::new(self.ast, self.scope.clone())
            .visit(node.child_by_field_name("type").unwrap())?;

        self.parameters.push(Parameter {
            id,
            typ: field_type,
        });

        Ok(())
    }

    fn visit_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.code.node_text(node).alloc_on(self.ast);
        let id = self.ast.make_id();

        self.scope
            .add_item(name, NamedItem::Parameter(id, node))
            .to_syntax_error(node)?;

        let placeholder = self.ast.make_id();
        self.placeholders.push(placeholder);

        self.parameters.push(Parameter {
            id,
            typ: self.ast.intern_type(Ty::Placeholder(placeholder)),
        });

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
            ExpressionVisitor::new(self.ast, self.scope.clone())
                .generate(node.child_by_field_name("body").unwrap())
                .and_then(|(expr, additional_items)| {
                    self.additional_items.extend(additional_items);
                    Ok(expr)
                })?,
        );

        self.return_type = Some(
            node.child_by_field_name("return_type")
                .map(|node| TypeVisitor::new(self.ast, self.scope.clone()).visit(node))
                .transpose()?
                .unwrap_or_else(|| {
                    let placeholder = self.ast.make_id();
                    self.placeholders.push(placeholder);
                    self.ast.intern_type(Ty::Placeholder(placeholder))
                }),
        );

        Ok(())
    }
}
