use crate::ast::{BinOp, Expr, ExprP, LetDeclaration, Lit, Statement, UnOp};
use crate::common::AluminaError;
use crate::name_resolution::resolver::ItemResolution;
use crate::name_resolution::scope::ScopeType;
use crate::parser::ParseCtx;
use crate::AluminaVisitor;
use crate::{
    ast::{BuiltinType, Ty, TyP},
    common::{SyntaxError, ToSyntaxError},
    name_resolution::{
        resolver::NameResolver,
        scope::{Item, Scope},
    },
    visitors::ScopedPathVisitor,
};

use super::types::TypeVisitor;
use super::UseClauseVisitor;

macro_rules! with_block_scope {
    ($self:ident, $body:expr) => {{
        let child_scope = $self.scope.anonymous_child(ScopeType::Block);
        let previous_scope = std::mem::replace(&mut $self.scope, child_scope);
        let result = $body;
        $self.scope = previous_scope;
        result
    }};
}

pub struct ExpressionVisitor<'gcx, 'src> {
    parse_ctx: ParseCtx<'gcx, 'src>,
    scope: Scope<'gcx, 'src>,
}

impl<'gcx, 'src> ExpressionVisitor<'gcx, 'src> {
    pub fn new(scope: Scope<'gcx, 'src>) -> Self {
        ExpressionVisitor {
            parse_ctx: scope
                .parse_ctx()
                .expect("cannot run on scope without parse context"),
            scope,
        }
    }

    fn visit_ref(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<ExprP<'gcx>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let expr = match resolver
            .resolve_item(self.scope.clone(), path)
            .to_syntax_error(node)?
        {
            ItemResolution::Item(Item::Function(fun, _, _)) => Expr::Function(fun),
            ItemResolution::Item(Item::Variable(var)) => Expr::Local(var),
            ItemResolution::Item(Item::Parameter(var, _)) => Expr::Local(var),
            ItemResolution::Defered(sym, name) => {
                let name = self.parse_ctx.alloc_str(name.0);
                Expr::DeferredFunction(sym, name)
            }
            a => panic!("{:?}", a),
        };

        Ok(self.parse_ctx.alloc_expr(expr))
    }
}

impl<'gcx, 'src> ExpressionVisitor<'gcx, 'src> {
    fn visit_statement(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<Option<Statement<'gcx>>, SyntaxError<'src>> {
        let result = match node.kind() {
            "empty_statement" => None,
            "let_declaration" => {
                let name = self
                    .parse_ctx
                    .node_text(node.child_by_field_name("name").unwrap());
                let id = self.parse_ctx.make_id();
                let typ = node
                    .child_by_field_name("type")
                    .map(|n| TypeVisitor::new(self.scope.clone()).visit(n))
                    .transpose()?;

                let value = node
                    .child_by_field_name("value")
                    .map(|n| self.visit(n))
                    .transpose()?;

                self.scope
                    .add_item(name, Item::Variable(id))
                    .to_syntax_error(node)?;

                let let_decl = LetDeclaration { id, typ, value };

                Some(Statement::LetDeclaration(let_decl))
            }
            "use_declaration" => {
                UseClauseVisitor::new(self.scope.clone())
                    .visit(node.child_by_field_name("argument").unwrap())?;
                None
            }
            "expression_statement" => Some(Statement::Expression(
                self.visit(node.child_by_field_name("inner").unwrap())?,
            )),
            _ => unimplemented!(),
        };

        Ok(result)
    }
}

impl<'gcx, 'src> AluminaVisitor<'src> for ExpressionVisitor<'gcx, 'src> {
    type ReturnType = Result<ExprP<'gcx>, SyntaxError<'src>>;

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
                None => self.parse_ctx.alloc_expr(Expr::Void),
            }
        });

        let result = Expr::Block(self.parse_ctx.alloc_range(statements), return_expression);
        Ok(self.parse_ctx.alloc_expr(result))
    }

    fn visit_integer_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self
            .parse_ctx
            .node_text(node)
            .parse()
            .map_err(|_| AluminaError::InvalidLiteral)
            .to_syntax_error(node)?;

        Ok(self.parse_ctx.alloc_expr(Expr::Lit(Lit::Int(value))))
    }

    fn visit_boolean_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self
            .parse_ctx
            .node_text(node)
            .parse()
            .map_err(|_| AluminaError::InvalidLiteral)
            .to_syntax_error(node)?;

        Ok(self.parse_ctx.alloc_expr(Expr::Lit(Lit::Bool(value))))
    }

    fn visit_void_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self.parse_ctx.alloc_expr(Expr::Void))
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
            .parse_ctx
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
            ">>" => BinOp::Rsh,
            "+" => BinOp::Plus,
            "-" => BinOp::Minus,
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,
            _ => unimplemented!(),
        };
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;

        Ok(self.parse_ctx.alloc_expr(Expr::Binary(lhs, op, rhs)))
    }

    fn visit_assignment_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field_name("left").unwrap())?;
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;

        Ok(self.parse_ctx.alloc_expr(Expr::Assign(lhs, rhs)))
    }

    fn visit_compound_assignment_expr(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        let lhs = self.visit(node.child_by_field_name("left").unwrap())?;
        let op = match self
            .parse_ctx
            .node_text(node.child_by_field_name("operator").unwrap())
        {
            "&&=" => BinOp::And,
            "||=" => BinOp::Or,
            "&=" => BinOp::BitAnd,
            "|=" => BinOp::BitOr,
            "^=" => BinOp::BitXor,
            "<<=" => BinOp::LShift,
            ">>=" => BinOp::Rsh,
            "+=" => BinOp::Plus,
            "-=" => BinOp::Minus,
            "*=" => BinOp::Mul,
            "/=" => BinOp::Div,
            "%=" => BinOp::Mod,
            _ => unimplemented!(),
        };
        let rhs = self.visit(node.child_by_field_name("right").unwrap())?;

        Ok(self.parse_ctx.alloc_expr(Expr::AssignOp(op, lhs, rhs)))
    }

    fn visit_call_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let func = self.visit(node.child_by_field_name("function").unwrap())?;
        let mut arguments = Vec::new();

        let arguments_node = node.child_by_field_name("arguments").unwrap();
        let mut cursor = arguments_node.walk();
        for node in arguments_node.children_by_field_name("inner", &mut cursor) {
            arguments.push(self.visit(node)?);
        }

        let result = Expr::Call(func, self.parse_ctx.alloc_range(arguments));
        Ok(self.parse_ctx.alloc_expr(result))
    }

    fn visit_tuple_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field_name("element", &mut cursor) {
            elements.push(self.visit(node)?);
        }

        let result = match elements[..] {
            [] => self.parse_ctx.alloc_expr(Expr::Void),
            [e] => e,
            _ => self
                .parse_ctx
                .alloc_expr(Expr::Tuple(self.parse_ctx.alloc_range(elements))),
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
            .parse_ctx
            .node_text(node.child_by_field_name("operator").unwrap())
        {
            "-" => UnOp::Neg,
            "!" => UnOp::Not,
            _ => unimplemented!(),
        };
        Ok(self.parse_ctx.alloc_expr(Expr::Unary(op, value)))
    }

    fn visit_reference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(self.parse_ctx.alloc_expr(Expr::Ref(value)))
    }

    fn visit_dereference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(self.parse_ctx.alloc_expr(Expr::Deref(value)))
    }

    fn visit_field_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;

        let field = node.child_by_field_name("field").unwrap();
        let field_value = self.parse_ctx.node_text(field);

        let result = match field.kind() {
            "identifier" => Expr::Field(value, self.parse_ctx.alloc_str(field_value)),
            "integer_literal" => Expr::TupleIndex(value, field_value.parse().unwrap()),
            _ => unreachable!(),
        };

        Ok(self.parse_ctx.alloc_expr(result))
    }

    fn visit_if_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let condition = self.visit(node.child_by_field_name("condition").unwrap())?;
        let consequence = self.visit(node.child_by_field_name("consequence").unwrap())?;
        let alternative = match node.child_by_field_name("alternative") {
            Some(node) => self.visit(node)?,
            None => self.parse_ctx.alloc_expr(Expr::Void),
        };

        Ok(self
            .parse_ctx
            .alloc_expr(Expr::If(condition, consequence, alternative)))
    }

    fn visit_generic_function(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("function").unwrap())?;

        let mut type_visitor = TypeVisitor::new(self.scope.clone());

        let arguments_node = node.child_by_field_name("type_arguments").unwrap();
        let mut cursor = arguments_node.walk();
        let arguments = arguments_node
            .children_by_field_name("type", &mut cursor)
            .map(|child| type_visitor.visit(child))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(self.parse_ctx.alloc_expr(Expr::GenericFunction(
            value,
            self.parse_ctx.alloc_slice(arguments.as_slice()),
        )))
    }

    fn visit_type_cast_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        let typ = TypeVisitor::new(self.scope.clone())
            .visit(node.child_by_field_name("type").unwrap())?;

        Ok(self.parse_ctx.alloc_expr(Expr::Cast(value, typ)))
    }

    fn visit_struct_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let typ = TypeVisitor::new(self.scope.clone())
            .visit(node.child_by_field_name("name").unwrap())?;

        let initializer_node = node.child_by_field_name("arguments").unwrap();
        let temporary = self.parse_ctx.make_id();
        let mut statements = vec![Statement::LetDeclaration(LetDeclaration {
            id: temporary,
            typ: Some(typ),
            value: None,
        })];

        let temporary_p = self.parse_ctx.alloc_expr(Expr::Local(temporary));

        with_block_scope!(self, {
            let mut cursor = initializer_node.walk();

            for node in initializer_node.children_by_field_name("item", &mut cursor) {
                let field = self
                    .parse_ctx
                    .node_text(node.child_by_field_name("field").unwrap());
                let value = self.visit(node.child_by_field_name("value").unwrap())?;

                statements.push(Statement::Expression(
                    self.parse_ctx.alloc_expr(Expr::Assign(
                        self.parse_ctx
                            .alloc_expr(Expr::Field(temporary_p, self.parse_ctx.alloc_str(field))),
                        value,
                    )),
                ));
            }
        });

        Ok(self.parse_ctx.alloc_expr(Expr::Block(
            self.parse_ctx.alloc_range(statements),
            temporary_p,
        )))
    }
}
