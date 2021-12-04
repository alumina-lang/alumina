use crate::ast::AstCtx;
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
}


impl<'ast, 'src> ExpressionVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>) -> Self {
        ExpressionVisitor {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
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
            ItemResolution::Item(NamedItem::Function(fun, _, _)) => Expr::Function(fun),
            ItemResolution::Item(NamedItem::Variable(var)) => Expr::Local(var),
            ItemResolution::Item(NamedItem::Parameter(var, _)) => Expr::Local(var),
            ItemResolution::Defered(sym, name) => {
                let name = name.0.alloc_on(self.ast);
                Expr::DeferredFunction(sym, name)
            }
            a => panic!("{:?}", a),
        };

        Ok(expr.alloc_on(self.ast))
    }
}

impl<'ast, 'src> ExpressionVisitor<'ast, 'src> {
    fn visit_statement(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<Option<Statement<'ast>>, SyntaxError<'src>> {
        let result = match node.kind() {
            "empty_statement" => None,
            "let_declaration" => {
                let name = self
                    .code
                    .node_text(node.child_by_field_name("name").unwrap());
                let id = self.ast.make_id();
                let typ = node
                    .child_by_field_name("type")
                    .map(|n| TypeVisitor::new(self.ast, self.scope.clone()).visit(n))
                    .transpose()?;

                let value = node
                    .child_by_field_name("value")
                    .map(|n| self.visit(n))
                    .transpose()?;

                self.scope
                    .add_item(name, NamedItem::Variable(id))
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

        let statements = statements.alloc_on(self.ast);
        let result = Expr::Block(statements, return_expression);

        Ok(result.alloc_on(self.ast))
    }

    fn visit_integer_literal(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let value = self
            .code
            .node_text(node)
            .parse()
            .map_err(|_| AluminaError::InvalidLiteral)
            .to_syntax_error(node)?;

        Ok(Expr::Lit(Lit::Int(value)).alloc_on(self.ast))
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
            ">>" => BinOp::Rsh,
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
            ">>=" => BinOp::Rsh,
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
            _ => unimplemented!(),
        };
        Ok((Expr::Unary(op, value).alloc_on(self.ast)))
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

        Ok((Expr::Cast(value, typ).alloc_on(self.ast)))
    }

    fn visit_struct_expression(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let typ = TypeVisitor::new(self.ast, self.scope.clone())
            .visit(node.child_by_field_name("name").unwrap())?;

        let initializer_node = node.child_by_field_name("arguments").unwrap();
        let temporary = self.ast.make_id();
        let mut statements = vec![Statement::LetDeclaration(LetDeclaration {
            id: temporary,
            typ: Some(typ),
            value: None,
        })];

        let temporary_p = Expr::Local(temporary).alloc_on(self.ast);

        with_block_scope!(self, {
            let mut cursor = initializer_node.walk();

            for node in initializer_node.children_by_field_name("item", &mut cursor) {
                let field = self
                    .code
                    .node_text(node.child_by_field_name("field").unwrap())
                    .alloc_on(self.ast);
                let value = self.visit(node.child_by_field_name("value").unwrap())?;

                statements.push(Statement::Expression(
                    Expr::Assign(Expr::Field(temporary_p, field).alloc_on(self.ast), value)
                        .alloc_on(self.ast),
                ));
            }
        });

        Ok(Expr::Block(statements.alloc_on(self.ast), temporary_p).alloc_on(self.ast))
    }
}
