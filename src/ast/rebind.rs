use std::collections::HashMap;

use crate::{
    ast::{Expr, FieldInitializer, FnKind},
    common::{AluminaError, ArenaAllocatable},
};

use super::{AstCtx, AstId, ExprP, Statement, TyP};

pub struct Rebinder<'ast> {
    pub ast: &'ast AstCtx<'ast>,
    pub replacements: HashMap<AstId, TyP<'ast>>,
}

impl<'ast> Rebinder<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, replacements: HashMap<AstId, TyP<'ast>>) -> Self {
        Self { ast, replacements }
    }

    pub fn visit_typ(&mut self, typ: TyP<'ast>) -> Result<TyP<'ast>, AluminaError> {
        use super::Ty::*;
        let kind = match typ {
            Placeholder(id) => match self.replacements.get(id) {
                Some(typ) => return Ok(typ),
                None => Placeholder(*id),
            },
            Pointer(inner, is_const) => Pointer(self.visit_typ(inner)?, *is_const),
            Slice(inner, is_const) => Slice(self.visit_typ(inner)?, *is_const),
            Array(inner, len) => Array(self.visit_typ(inner)?, *len),
            Tuple(elems) => Tuple(
                elems
                    .iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            Fn(elems, ret) => Fn(
                elems
                    .iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                self.visit_typ(ret)?,
            ),

            GenericType(item, args) => GenericType(
                item,
                args.iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),

            NamedType(_) | Builtin(_) | Protocol(_) => return Ok(typ),
        };

        Ok(self.ast.intern_type(kind))
    }

    pub fn visit_stmt(&mut self, stmt: &Statement<'ast>) -> Result<Statement<'ast>, AluminaError> {
        use super::StatementKind::*;

        let kind = match &stmt.kind {
            Expression(expr) => Expression(self.visit_expr(expr)?),
            LetDeclaration(decl) => LetDeclaration(crate::ast::LetDeclaration {
                id: decl.id,
                typ: decl.typ.map(|t| self.visit_typ(t)).transpose()?,
                value: decl.value.map(|v| self.visit_expr(v)).transpose()?,
            }),
        };

        let result = Statement {
            kind,
            span: stmt.span,
        };

        Ok(result)
    }

    pub fn visit_expr(&mut self, expr: ExprP<'ast>) -> Result<ExprP<'ast>, AluminaError> {
        use super::ExprKind::*;
        let kind = match expr.kind {
            Call(callee, args) => Call(
                self.visit_expr(callee)?,
                args.iter()
                    .map(|e| self.visit_expr(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            Tuple(args) => Tuple(
                args.iter()
                    .map(|e| self.visit_expr(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            Array(args) => Array(
                args.iter()
                    .map(|e| self.visit_expr(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            DeferedMacro(_, _) => {
                unreachable!("macros should have been expanded by now")
            }
            EtCetera(_) => {
                unreachable!("macros should have been expanded by now")
            }
            Block(statements, ret) => {
                let mut new_statements = Vec::new();
                for statement in statements {
                    new_statements.push(self.visit_stmt(statement)?);
                }
                Block(new_statements.alloc_on(self.ast), self.visit_expr(ret)?)
            }
            Binary(op, lhs, rhs) => Binary(op, self.visit_expr(lhs)?, self.visit_expr(rhs)?),
            Ref(inner) => Ref(self.visit_expr(inner)?),
            Deref(inner) => Deref(self.visit_expr(inner)?),

            Unary(op, inner) => Unary(op, self.visit_expr(inner)?),
            Assign(lhs, rhs) => Assign(self.visit_expr(lhs)?, self.visit_expr(rhs)?),
            AssignOp(op, lhs, rhs) => AssignOp(op, self.visit_expr(lhs)?, self.visit_expr(rhs)?),
            Loop(inner) => Loop(self.visit_expr(inner)?),
            Break(inner) => Break(inner.map(|i| self.visit_expr(i)).transpose()?),
            Return(inner) => Return(inner.map(|i| self.visit_expr(i)).transpose()?),
            Defer(inner) => Defer(self.visit_expr(inner)?),
            Field(a, name, assoc_fn) => Field(self.visit_expr(a)?, name, assoc_fn),
            Struct(ty, inits) => {
                let inits: Vec<_> = inits
                    .iter()
                    .map(|init| {
                        self.visit_expr(init.value).map(|value| FieldInitializer {
                            name: init.name,
                            value,
                            span: init.span,
                        })
                    })
                    .collect::<Result<_, _>>()?;

                Struct(ty, inits.alloc_on(self.ast))
            }
            TupleIndex(inner, idx) => TupleIndex(self.visit_expr(inner)?, idx),
            Index(inner, idx) => Index(self.visit_expr(inner)?, self.visit_expr(idx)?),
            RangeIndex(inner, lower, upper) => RangeIndex(
                self.visit_expr(inner)?,
                lower.map(|i| self.visit_expr(i)).transpose()?,
                upper.map(|i| self.visit_expr(i)).transpose()?,
            ),
            If(condition, then, els) => If(
                self.visit_expr(condition)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
            ),
            Cast(inner, typ) => Cast(self.visit_expr(inner)?, self.visit_typ(typ)?),
            Defered(ref def) => Defered(crate::ast::Defered {
                typ: self.visit_typ(def.typ)?,
                name: def.name,
            }),
            Fn(ref kind, generic_args) => {
                let kind = match kind {
                    FnKind::Normal(_) => kind.clone(),
                    FnKind::Defered(def) => FnKind::Defered(crate::ast::Defered {
                        typ: self.visit_typ(def.typ)?,
                        name: def.name,
                    }),
                };

                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_typ(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Fn(kind, generic_args)
            }
            Local(_) | Continue | EnumValue(_, _) | Lit(_) | Void | Static(_) | Const(_) => {
                expr.kind.clone()
            }
        };

        let result = Expr {
            kind,
            span: expr.span,
        };

        Ok(result.alloc_on(self.ast))
    }
}
