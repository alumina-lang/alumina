use crate::ast::{BinOp, Expression, ExpressionP, LetDeclaration, Statement, UnOp};
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
    ) -> Result<ExpressionP<'gcx>, SyntaxError<'src>> {
        let mut visitor = ScopedPathVisitor::new(self.scope.clone());
        let path = visitor.visit(node)?;
        let mut resolver = NameResolver::new();

        let expr = match resolver
            .resolve_item(self.scope.clone(), path)
            .to_syntax_error(node)?
        {
            ItemResolution::Item(Item::Function(fun, _, _)) => Expression::Function(fun),
            ItemResolution::Item(Item::Variable(var)) => Expression::Variable(var),
            ItemResolution::Defered(sym, name) => {
                let name = self.parse_ctx.alloc_str(name.0);
                Expression::DeferredFunction(sym, name)
            }
            _ => unimplemented!(),
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
                let var = self.parse_ctx.make_variable();
                let typ = node
                    .child_by_field_name("type")
                    .map(|n| TypeVisitor::new(self.scope.clone()).visit(n))
                    .transpose()?;

                let value = node
                    .child_by_field_name("value")
                    .map(|n| self.visit(n))
                    .transpose()?;

                self.scope
                    .add_item(name, Item::Variable(var))
                    .to_syntax_error(node)?;

                let let_decl = LetDeclaration { var, typ, value };

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
    type ReturnType = Result<ExpressionP<'gcx>, SyntaxError<'src>>;

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
                None => self.parse_ctx.alloc_expr(Expression::Void),
            }
        });

        let result = Expression::Block(self.parse_ctx.alloc_range(statements), return_expression);
        Ok(self.parse_ctx.alloc_expr(result))
    }

    fn visit_integer_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.parse_ctx.alloc_str(self.parse_ctx.node_text(node));

        Ok(self.parse_ctx.alloc_expr(Expression::IntegerLiteral(value)))
    }

    fn visit_void_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Ok(self.parse_ctx.alloc_expr(Expression::Void))
    }

    fn visit_parenthesized_expression(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
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

        Ok(self.parse_ctx.alloc_expr(Expression::Binary(lhs, op, rhs)))
    }

    fn visit_call_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let func = self.visit(node.child_by_field_name("function").unwrap())?;
        let mut arguments = Vec::new();

        let arguments_node = node.child_by_field_name("arguments").unwrap();
        let mut cursor = arguments_node.walk();
        for node in arguments_node.children_by_field_name("inner", &mut cursor) {
            arguments.push(self.visit(node)?);
        }

        let result = Expression::Call(func, self.parse_ctx.alloc_range(arguments));
        Ok(self.parse_ctx.alloc_expr(result))
    }

    fn visit_tuple_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut elements = Vec::new();

        let mut cursor = node.walk();
        for node in node.children_by_field_name("element", &mut cursor) {
            elements.push(self.visit(node)?);
        }

        let result = match elements[..] {
            [] => self.parse_ctx.alloc_expr(Expression::Void),
            [e] => e,
            _ => self
                .parse_ctx
                .alloc_expr(Expression::Tuple(self.parse_ctx.alloc_range(elements))),
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
        Ok(self.parse_ctx.alloc_expr(Expression::Unary(op, value)))
    }

    fn visit_reference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(self.parse_ctx.alloc_expr(Expression::Ref(value)))
    }

    fn visit_dereference_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self.visit(node.child_by_field_name("value").unwrap())?;
        Ok(self.parse_ctx.alloc_expr(Expression::Deref(value)))
    }
}
