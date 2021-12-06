use crate::ast::{AstCtx, FieldInitializer};
use crate::ast::{BinOp, Expr, ExprP, LetDeclaration, Lit, Statement, UnOp};
use crate::common::AluminaError;
use crate::common::ArenaAllocatable;
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
use super::BuiltinType;

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
        }
    }

    fn visit_ref(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<ExprP<'ast>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let expr = match resolver
            .resolve_item(self.scope.clone(), path)
            .to_syntax_error(node)?
        {
            ItemResolution::Item(NamedItem::Function(fun, _, _)) => Expr::Fn(fun),
            ItemResolution::Item(NamedItem::Variable(var)) => Expr::Local(var),
            ItemResolution::Item(NamedItem::Parameter(var, _)) => Expr::Local(var),
            ItemResolution::Defered(sym, name) => {
                let name = name.0.alloc_on(self.ast);
                Expr::DeferredFunction(sym, name)
            }
            a => panic!("{:?} at {:?}", a, node),
        };

        Ok(expr.alloc_on(self.ast))
    }
}

impl<'ast, 'src> ExpressionVisitor<'ast, 'src> {
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
                    .node_text(inner.child_by_field_name("name").unwrap());
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
                    .add_item(name, NamedItem::Variable(id))
                    .to_syntax_error(inner)?;

                let let_decl = LetDeclaration { id, typ, value };

                Some(Statement::LetDeclaration(let_decl))
            }
            "use_declaration" => {
                UseClauseVisitor::new(self.scope.clone())
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
}

impl<'ast, 'src> AluminaVisitor<'src> for ExpressionVisitor<'ast, 'src> {
    type ReturnType = Result<ExprP<'ast>, SyntaxError<'src>>;

    fn visit_block(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let mut statements = Vec::new();

        let return_expression = with_block_scope!(self, {
            for node in node.children_by_field_name("statements", &mut cursor) {
                if let Some(stmt) = self.visit_statement(node)? {
                    statements.push(stmt);
                }
            }

            match node.child_by_field_name("result") {
                Some(return_expression) => self.visit(return_expression)?,
                None => Expr::Void.alloc_on(self.ast),
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

    fn visit_integer_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (remainder, kind) = match self.code.node_text(node) {
            v if v.ends_with("u8") => (&v[..v.len() - 2], Some(BuiltinType::U8)),
            v if v.ends_with("u16") => (&v[..v.len() - 3], Some(BuiltinType::U16)),
            v if v.ends_with("u32") => (&v[..v.len() - 3], Some(BuiltinType::U32)),
            v if v.ends_with("u64") => (&v[..v.len() - 3], Some(BuiltinType::U64)),
            v if v.ends_with("i8") => (&v[..v.len() - 2], Some(BuiltinType::I8)),
            v if v.ends_with("i16") => (&v[..v.len() - 3], Some(BuiltinType::I16)),
            v if v.ends_with("i32") => (&v[..v.len() - 3], Some(BuiltinType::I32)),
            v if v.ends_with("i64") => (&v[..v.len() - 3], Some(BuiltinType::I64)),
            v if v.ends_with("usize") => (&v[..v.len() - 5], Some(BuiltinType::USize)),
            v if v.ends_with("isize") => (&v[..v.len() - 5], Some(BuiltinType::ISize)),
            v => (v, None),
        };

        let value = remainder
            .parse()
            .map_err(|_| AluminaError::InvalidLiteral)
            .to_syntax_error(node)?;

        Ok(Expr::Lit(Lit::Int(value, kind)).alloc_on(self.ast))
    }

    fn visit_float_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let (remainder, kind) = match self.code.node_text(node) {
            v if v.ends_with("f32") => (&v[..v.len() - 3], Some(BuiltinType::F32)),
            v if v.ends_with("f64") => (&v[..v.len() - 3], Some(BuiltinType::F64)),
            v => (v, None),
        };

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
            .map_err(|_| AluminaError::InvalidLiteral)
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

        Ok(Expr::Binary(lhs, op, rhs).alloc_on(self.ast))
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
        let field_value = self.code.node_text(field);

        let result = match field.kind() {
            "identifier" => Expr::Field(value, field_value.alloc_on(self.ast)),
            "integer_literal" => Expr::TupleIndex(value, field_value.parse().unwrap()),
            _ => unreachable!(),
        };

        Ok(result.alloc_on(self.ast))
    }

    fn visit_index_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        let index = self.visit(node.child_by_field_name("index").unwrap())?;
        let result = Expr::Index(value, index);

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
        let value = self.visit(node.child_by_field_name("function").unwrap())?;

        let mut type_visitor = TypeVisitor::new(self.ast, self.scope.clone());

        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| type_visitor.visit(child))
            .collect::<Result<Vec<_>, _>>()?
            .alloc_on(self.ast);

        let result = Expr::GenericFunction(value, arguments);
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
            return Err(AluminaError::BreakOutsideOfLoop).to_syntax_error(node);
        }

        let inner = node
            .child_by_field_name("inner")
            .map(|n| self.visit(n))
            .transpose()?;

        Ok(Expr::Break(inner).alloc_on(self.ast))
    }

    fn visit_continue_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_loop {
            return Err(AluminaError::ContinueOutsideOfLoop).to_syntax_error(node);
        }
        Ok(Expr::Continue.alloc_on(self.ast))
    }

    fn visit_struct_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let typ = TypeVisitor::new(self.ast, self.scope.clone())
            .visit(node.child_by_field_name("name").unwrap())?;

        let initializer_node = node.child_by_field_name("arguments").unwrap();
        let mut field_initializers = Vec::new();

        with_block_scope!(self, {
            let mut cursor = initializer_node.walk();

            for node in initializer_node.children_by_field_name("item", &mut cursor) {
                let field = self
                    .code
                    .node_text(node.child_by_field_name("field").unwrap())
                    .alloc_on(self.ast);
                let value = self.visit(node.child_by_field_name("value").unwrap())?;

                field_initializers.push(FieldInitializer {
                    name: field.alloc_on(self.ast),
                    value,
                });
            }
        });

        Ok(Expr::Struct(typ, field_initializers.alloc_on(self.ast)).alloc_on(self.ast))
    }
}

fn parse_string_literal(lit: &str) -> Result<String, AluminaError> {
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
                    return Err(AluminaError::InvalidEscapeSequence);
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
                            .map_err(|_| AluminaError::InvalidEscapeSequence)?,
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
                            .map_err(|_| AluminaError::InvalidEscapeSequence)?,
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
        _ => Err(AluminaError::InvalidEscapeSequence),
    }
}
