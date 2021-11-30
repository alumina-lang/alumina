use crate::ast::{Expression, ExpressionP, Statement};
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

macro_rules! with_block_scope {
    ($self:ident, $body:expr) => {{
        let child_scope =
            Scope::with_parent(ScopeType::Block, $self.scope.path(), $self.scope.clone());
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
}

impl<'gcx, 'src> ExpressionVisitor<'gcx, 'src> {
    fn visit_statement(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Result<Statement<'gcx>, SyntaxError<'src>> {
        unimplemented!()
    }
}

impl<'gcx, 'src> AluminaVisitor<'src> for ExpressionVisitor<'gcx, 'src> {
    type ReturnType = Result<ExpressionP<'gcx>, SyntaxError<'src>>;

    fn visit_block(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let mut expressions = Vec::new();

        let return_expression = with_block_scope!(self, {
            for node in node.children_by_field_name("statements", &mut cursor) {
                // expressions.push(self.visit(node)?);
            }

            match node.child_by_field_name("result") {
                Some(return_expression) => self.visit(return_expression)?,
                None => self.parse_ctx.alloc_expr(Expression::Void),
            }
        });

        let result = Expression::Block(self.parse_ctx.alloc_range(expressions), return_expression);
        Ok(self.parse_ctx.alloc_expr(result))
    }
}
