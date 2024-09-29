use crate::ast::{
    AstCtx, Bound, Expr, ExprP, FieldInitializer, FnKind, Id, Placeholder, ProtocolBounds,
    Statement, TyP,
};
use crate::common::{AluminaError, ArenaAllocatable, HashMap};

pub struct Rebinder<'ast> {
    pub ast: &'ast AstCtx<'ast>,
    pub replacements: HashMap<Id, TyP<'ast>>,
}

impl<'ast> Rebinder<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, replacements: HashMap<Id, TyP<'ast>>) -> Self {
        Self { ast, replacements }
    }

    pub fn visit_placeholder(
        &mut self,
        placeholder: &Placeholder<'ast>,
    ) -> Result<Placeholder<'ast>, AluminaError> {
        Ok(Placeholder {
            bounds: self.visit_bounds(&placeholder.bounds)?,
            default: placeholder.default.map(|d| self.visit_ty(d)).transpose()?,
            span: placeholder.span,
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
            ty: self.visit_ty(bound.ty)?,
        })
    }

    pub fn visit_ty(&mut self, ty: TyP<'ast>) -> Result<TyP<'ast>, AluminaError> {
        use crate::ast::Ty::*;
        let kind = match ty {
            Placeholder(id) => match self.replacements.get(id) {
                Some(ty) => Tag("dynamic", ty),
                None => Placeholder(*id),
            },
            Tag(tag, inner) => Tag(tag, self.visit_ty(inner)?),
            Pointer(inner, is_const) => Pointer(self.visit_ty(inner)?, *is_const),
            Slice(inner, is_const) => Slice(self.visit_ty(inner)?, *is_const),
            Array(inner, len) => Array(self.visit_ty(inner)?, self.visit_expr(len)?),
            Tuple(elems) => Tuple(
                elems
                    .iter()
                    .map(|e| self.visit_ty(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            FunctionPointer(elems, ret) => FunctionPointer(
                elems
                    .iter()
                    .map(|e| self.visit_ty(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                self.visit_ty(ret)?,
            ),
            FunctionProtocol(elems, ret) => FunctionProtocol(
                elems
                    .iter()
                    .map(|e| self.visit_ty(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                self.visit_ty(ret)?,
            ),
            Dyn(inner, is_const) => Dyn(
                inner
                    .iter()
                    .map(|e| self.visit_ty(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
                *is_const,
            ),
            TypeOf(inner) => TypeOf(self.visit_expr(inner)?),
            Generic(item, args) => Generic(
                item,
                args.iter()
                    .map(|e| self.visit_ty(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            Defered(super::Defered { ty, name }) => Defered(super::Defered {
                ty: self.visit_ty(ty)?,
                name,
            }),
            When(cond, then, els) => When(
                self.visit_expr(cond)?,
                self.visit_ty(then)?,
                self.visit_ty(els)?,
            ),
            EtCetera(inner) => EtCetera(self.visit_ty(inner)?),
            Deref(inner) => Deref(self.visit_ty(inner)?),
            TupleIndex(inner, idx) => TupleIndex(self.visit_ty(inner)?, self.visit_expr(idx)?),
            Item(_) | Builtin(_) => return Ok(ty),
        };

        Ok(self.ast.intern_type(kind))
    }

    pub fn visit_stmt(&mut self, stmt: &Statement<'ast>) -> Result<Statement<'ast>, AluminaError> {
        use crate::ast::StatementKind::*;

        let kind = match &stmt.kind {
            Expression(expr) => Expression(self.visit_expr(expr)?),
            LetDeclaration(decl) => LetDeclaration(crate::ast::LetDeclaration {
                id: decl.id,
                ty: decl.ty.map(|t| self.visit_ty(t)).transpose()?,
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
        use crate::ast::ExprKind::*;
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
            Macro(_, _) | MacroInvocation(_, _) | EtCeteraMacro(_) => {
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
            Yield(inner) => Yield(inner.map(|i| self.visit_expr(i)).transpose()?),
            Defer(inner) => Defer(self.visit_expr(inner)?),
            Field(a, name, assoc_fn, generic_args) => {
                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_ty(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Field(self.visit_expr(a)?, name, assoc_fn, generic_args)
            }
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
            StaticFor(id, range, body) => {
                StaticFor(id, self.visit_expr(range)?, self.visit_expr(body)?)
            }
            Cast(inner, ty) => Cast(self.visit_expr(inner)?, self.visit_ty(ty)?),
            Defered(ref def) => Defered(crate::ast::Defered {
                ty: self.visit_ty(def.ty)?,
                name: def.name,
            }),
            Fn(ref kind, generic_args) => {
                let kind = match kind {
                    FnKind::Normal(_) => *kind,
                    FnKind::Closure(..) => *kind,
                    FnKind::Defered(def) => FnKind::Defered(crate::ast::Defered {
                        ty: self.visit_ty(def.ty)?,
                        name: def.name,
                    }),
                };

                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_ty(e))
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
                            .map(|e| self.visit_ty(e))
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
                            .map(|e| self.visit_ty(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Const(item, generic_args)
            }
            StaticIf(cond, then, els) => StaticIf(
                self.visit_expr(cond)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
            ),
            TypeCheck(lhs, rhs) => TypeCheck(self.visit_expr(lhs)?, self.visit_ty(rhs)?),
            EtCetera(inner) => EtCetera(self.visit_expr(inner)?),
            Local(_) | BoundParam(_, _, _) | Continue | EnumValue(_, _) | Lit(_) | Void => {
                expr.kind
            }
            Tag(tag, inner) => Tag(tag, self.visit_expr(inner)?),
        };

        let result = Expr {
            kind,
            span: expr.span,
        };

        Ok(result.alloc_on(self.ast))
    }
}
