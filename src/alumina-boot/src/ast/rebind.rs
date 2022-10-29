use std::collections::HashMap;

use crate::{
    ast::{Bound, Expr, FieldInitializer, FnKind, StaticIfCondition},
    common::{AluminaError, ArenaAllocatable},
};

use super::{AstCtx, AstId, ExprP, Placeholder, ProtocolBounds, Statement, TyP};

pub struct Rebinder<'ast> {
    pub ast: &'ast AstCtx<'ast>,
    pub replacements: HashMap<AstId, TyP<'ast>>,
}

impl<'ast> Rebinder<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, replacements: HashMap<AstId, TyP<'ast>>) -> Self {
        Self { ast, replacements }
    }

    pub fn visit_placeholder(
        &mut self,
        placeholder: &Placeholder<'ast>,
    ) -> Result<Placeholder<'ast>, AluminaError> {
        Ok(Placeholder {
            bounds: self.visit_bounds(&placeholder.bounds)?,
            default: placeholder.default.map(|d| self.visit_typ(d)).transpose()?,
            id: placeholder.id,
        })
    }

    pub fn visit_bounds(
        &mut self,
        bounds: &ProtocolBounds<'ast>,
    ) -> Result<ProtocolBounds<'ast>, AluminaError> {
        let new_bounds = bounds
            .bounds
            .iter()
            .map(|b| self.visit_bound(b))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(ProtocolBounds {
            kind: bounds.kind,
            bounds: new_bounds.alloc_on(self.ast),
        })
    }

    pub fn visit_bound(&mut self, bound: &Bound<'ast>) -> Result<Bound<'ast>, AluminaError> {
        Ok(Bound {
            negated: bound.negated,
            span: bound.span,
            typ: self.visit_typ(bound.typ)?,
        })
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
            FunctionPointer(elems, ret) => FunctionPointer(
                elems
                    .iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                self.visit_typ(ret)?,
            ),
            FunctionProtocol(elems, ret) => FunctionProtocol(
                elems
                    .iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                self.visit_typ(ret)?,
            ),
            Dyn(inner, is_const) => Dyn(
                inner
                    .iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                *is_const,
            ),
            TypeOf(inner) => TypeOf(self.visit_expr(inner)?),
            Generic(item, args) => Generic(
                item,
                args.iter()
                    .map(|e| self.visit_typ(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            Defered(super::Defered { typ, name }) => Defered(super::Defered {
                typ: self.visit_typ(typ)?,
                name,
            }),
            When(cond, then, els) => When(
                StaticIfCondition {
                    bounds: self.visit_bounds(&cond.bounds)?,
                    typ: self.visit_typ(typ)?,
                },
                self.visit_typ(then)?,
                self.visit_typ(els)?,
            ),
            NamedFunction(_) | NamedType(_) | Builtin(_) | Protocol(_) => return Ok(typ),
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
            Range(lower, upper, inclusive) => Range(
                lower.map(|i| self.visit_expr(i)).transpose()?,
                upper.map(|i| self.visit_expr(i)).transpose()?,
                inclusive,
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
                    FnKind::Closure(..) => kind.clone(),
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
            Static(item, generic_args) => {
                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_typ(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Static(item, generic_args)
            }
            Const(item, generic_args) => {
                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_typ(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Const(item, generic_args)
            }
            StaticIf(ref cond, then, els) => {
                let cond = StaticIfCondition {
                    typ: self.visit_typ(cond.typ)?,
                    bounds: ProtocolBounds {
                        kind: cond.bounds.kind,
                        bounds: cond
                            .bounds
                            .bounds
                            .iter()
                            .map(|b| {
                                self.visit_typ(b.typ).map(|t| Bound {
                                    span: b.span,
                                    negated: b.negated,
                                    typ: t,
                                })
                            })
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    },
                };

                StaticIf(cond, self.visit_expr(then)?, self.visit_expr(els)?)
            }
            Local(_) | BoundParam(_, _, _) | Continue | EnumValue(_, _) | Lit(_) | Void => {
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
