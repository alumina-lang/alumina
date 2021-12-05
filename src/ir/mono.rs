use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;
use std::iter::{once, repeat};

use super::IrCtx;
use crate::ast::{expressions, BuiltinType};
use crate::common::ArenaAllocatable;
use crate::ir::FuncBodyCell;
use crate::{ast, common::AluminaError, ir};

macro_rules! builtin {
    ($self:expr, $name:ident) => {
        $self
            .mono_ctx
            .ir
            .intern_type(crate::ir::Ty::Builtin(crate::ast::BuiltinType::$name))
    };
}

pub struct ExpressionBuilder<'ir> {
    ir: &'ir ir::IrCtx<'ir>,
}

impl<'ir> ExpressionBuilder<'ir> {
    pub fn new(ir: &'ir ir::IrCtx<'ir>) -> Self {
        Self { ir }
    }

    pub fn local(&self, id: ir::IrId, typ: ir::TyP<'ir>) -> ir::ExprP<'ir> {
        ir::Expr::lvalue(ir::ExprKind::Local(id), typ).alloc_on(self.ir)
    }

    pub fn block(
        &self,
        statements: Vec<ir::Statement<'ir>>,
        ret: ir::ExprP<'ir>,
    ) -> ir::ExprP<'ir> {
        ir::Expr::rvalue(
            ir::ExprKind::Block(statements.alloc_on(self.ir), ret),
            ret.typ,
        )
        .alloc_on(self.ir)
    }

    pub fn assign(&self, lhs: ir::ExprP<'ir>, rhs: ir::ExprP<'ir>) -> ir::ExprP<'ir> {
        ir::Expr::rvalue(
            ir::ExprKind::Assign(lhs, rhs),
            self.ir.intern_type(ir::Ty::Builtin(BuiltinType::Void)),
        )
        .alloc_on(self.ir)
    }

    pub fn tuple_index(
        &self,
        tuple: ir::ExprP<'ir>,
        index: usize,
        typ: ir::TyP<'ir>,
    ) -> ir::ExprP<'ir> {
        let expr = ir::Expr {
            kind: ir::ExprKind::TupleIndex(tuple, index),
            value_type: tuple.value_type,
            typ,
        };

        expr.alloc_on(self.ir)
    }
}

pub struct MonoCtx<'ast, 'ir> {
    ir: &'ir ir::IrCtx<'ir>,
    id_map: HashMap<ast::AstId, ir::IrId>,
    finished: HashMap<MonomorphizeKey<'ast, 'ir>, ir::IRItemP<'ir>>,
}

impl<'ast, 'ir> MonoCtx<'ast, 'ir> {
    pub fn new(ir: &'ir ir::IrCtx<'ir>) -> Self {
        MonoCtx {
            ir,
            id_map: HashMap::new(),
            finished: HashMap::new(),
        }
    }

    fn map_id(&mut self, id: ast::AstId) -> ir::IrId {
        *self.id_map.entry(id).or_insert_with(|| self.ir.make_id())
    }

    pub fn into_inner(self) -> Vec<ir::IRItemP<'ir>> {
        self.finished.values().copied().collect()
    }
}

pub struct Monomorphizer<'a, 'ast, 'ir> {
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    slot_types: HashMap<ir::IrId, ir::TyP<'ir>>,
    builder: ExpressionBuilder<'ir>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphizeKey<'ast, 'ir>(ast::ItemP<'ast>, &'ir [ir::TyP<'ir>]);

impl<'a, 'ast, 'ir> Monomorphizer<'a, 'ast, 'ir> {
    pub fn new(mono_ctx: &'a mut MonoCtx<'ast, 'ir>) -> Self {
        let ir = mono_ctx.ir;

        Monomorphizer {
            mono_ctx,
            replacements: HashMap::new(),
            slot_types: HashMap::new(),
            builder: ExpressionBuilder::new(ir),
        }
    }

    pub fn with_replacements<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    ) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;

        Monomorphizer {
            mono_ctx,
            replacements,
            slot_types: HashMap::new(),
            builder: ExpressionBuilder::new(ir),
        }
    }

    pub fn monomorphize(
        &mut self,
        item: ast::ItemP<'ast>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        self.monomorphize_item(MonomorphizeKey(item, &[]))
    }

    pub fn monomorphize_item(
        &mut self,
        key: MonomorphizeKey<'ast, 'ir>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let item: ir::IRItemP = match self.mono_ctx.finished.entry(key.clone()) {
            // The cell may be empty at this point if we are dealing with recursive references
            // In this case, we will just return the item as is, but it will not
            // be populated until the top-level item is finished.
            Entry::Occupied(entry) => return Ok(entry.get()),
            Entry::Vacant(entry) => entry.insert(self.mono_ctx.ir.make_symbol()),
        };

        match key.0.get() {
            ast::Item::Function(func) => {
                if key.1.len() != func.placeholders.len() {
                    return Err(AluminaError::GenericParamCountMismatch(
                        func.placeholders.len(),
                        key.1.len(),
                    ));
                }

                let mut child = Self::with_replacements(
                    self.mono_ctx,
                    self.replacements
                        .iter()
                        .map(|(&k, &v)| (k, v))
                        .chain(
                            func.placeholders
                                .iter()
                                .zip(key.1.iter())
                                .map(|(&k, &v)| (k, v)),
                        )
                        .collect(),
                );

                let parameters = func
                    .parameters
                    .iter()
                    .map(|p| {
                        let param = ir::Parameter {
                            id: child.mono_ctx.map_id(p.id),
                            ty: child.monomorphize_type(p.ty)?,
                        };
                        child.slot_types.insert(param.id, param.ty);
                        Ok(param)
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                let return_type = child.monomorphize_type(func.return_type)?;
                let res = ir::IRItem::Function(ir::Function {
                    parameters: &parameters.alloc_on(child.mono_ctx.ir),
                    return_type,
                    body: FuncBodyCell::new(),
                });
                item.assign(res);

                // We need the item to be assigned before we monomorphize the body, as the
                // function can be recursive and we need to be able to get the signature for
                // typechecking purposes.

                let body = child.monomorphize_expr(
                    func.body.expect("extern function not supported"),
                    Some(return_type),
                )?;

                if body.typ != return_type {
                    return Err(AluminaError::TypeMismatch);
                }

                match item.get() {
                    ir::IRItem::Function(func) => func.body.assign(body),
                    _ => unreachable!(),
                }
            }
            ast::Item::Struct(s) => {
                if key.1.len() != s.placeholders.len() {
                    return Err(AluminaError::GenericParamCountMismatch(
                        s.placeholders.len(),
                        key.1.len(),
                    ));
                }

                let mut child = Self::with_replacements(
                    self.mono_ctx,
                    self.replacements
                        .iter()
                        .map(|(&k, &v)| (k, v))
                        .chain(
                            s.placeholders
                                .iter()
                                .zip(key.1.iter())
                                .map(|(&k, &v)| (k, v)),
                        )
                        .collect(),
                );

                let fields = s
                    .fields
                    .iter()
                    .map(|f| {
                        Ok(ir::Field {
                            name: f.name.alloc_on(child.mono_ctx.ir),
                            ty: child.monomorphize_type(f.ty)?,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                let res = ir::IRItem::Struct(ir::Struct {
                    fields: fields.alloc_on(self.mono_ctx.ir),
                });
                item.assign(res);
            }
        };

        Ok(item)
    }

    pub fn monomorphize_type(&mut self, typ: ast::TyP<'ast>) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *typ {
            // TODO: can coalesce same usize == u64 depending on platform here I guess
            ast::Ty::Builtin(kind) => ir::Ty::Builtin(kind),
            ast::Ty::Array(inner, len) => ir::Ty::Array(self.monomorphize_type(inner)?, len),
            ast::Ty::Pointer(inner) => ir::Ty::Pointer(self.monomorphize_type(inner)?),
            ast::Ty::Slice(inner) => ir::Ty::Slice(self.monomorphize_type(inner)?),
            ast::Ty::Extern(id) => ir::Ty::Extern(self.mono_ctx.map_id(id)),
            ast::Ty::Function(args, ret) => ir::Ty::Function(
                args.iter()
                    .map(|arg| self.monomorphize_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir),
                self.monomorphize_type(ret)?,
            ),
            ast::Ty::Tuple(items) => ir::Ty::Tuple(
                items
                    .iter()
                    .map(|arg| self.monomorphize_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir),
            ),

            ast::Ty::Placeholder(id) => *self
                .replacements
                .get(&id)
                .copied()
                .expect("unbound placeholder"),

            ast::Ty::NamedType(item) => {
                let key = MonomorphizeKey(item, &[]);
                let item = self.monomorphize_item(key)?;
                ir::Ty::NamedType(item)
            }
            ast::Ty::GenericType(item, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.monomorphize_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir);

                let key = MonomorphizeKey(item, args);
                let item = self.monomorphize_item(key)?;

                ir::Ty::NamedType(item)
            }
        };

        Ok(self.mono_ctx.ir.intern_type(result))
    }

    pub fn monomorphize_stmt(
        &mut self,
        stmt: &ast::Statement<'ast>,
    ) -> Result<Vec<ir::Statement<'ir>>, AluminaError> {
        let result = match stmt {
            ast::Statement::Expression(expr) => {
                let expr = self.monomorphize_expr(expr, None)?;
                vec![ir::Statement::Expression(expr)]
            }
            ast::Statement::LetDeclaration(decl) => {
                let id = self.mono_ctx.map_id(decl.id);
                let type_hint = decl.typ.map(|t| self.monomorphize_type(t)).transpose()?;
                let init = decl
                    .value
                    .map(|v| self.monomorphize_expr(v, type_hint))
                    .transpose()?;
                match (type_hint, init) {
                    (None, None) => return Err(AluminaError::TypeHintRequired),
                    (Some(ty), None) => {
                        self.slot_types.insert(id, ty);
                        vec![ir::Statement::LocalDef(id, ty)]
                    }
                    (_, Some(init)) => {
                        if !type_hint.is_none() && type_hint != Some(init.typ) {
                            return Err(AluminaError::TypeMismatch);
                        }

                        self.slot_types.insert(id, init.typ);

                        vec![
                            ir::Statement::LocalDef(id, init.typ),
                            ir::Statement::Expression(
                                self.builder.assign(self.builder.local(id, init.typ), init),
                            ),
                        ]
                    }
                }
            }
        };

        Ok(result)
    }

    pub fn monomorphize_block(
        &mut self,
        statements: &'ast [ast::Statement<'ast>],
        ret: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let statements = statements
            .iter()
            .map(|stmt| self.monomorphize_stmt(stmt))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>()
            .alloc_on(self.mono_ctx.ir);

        let ret = self.monomorphize_expr(ret, type_hint)?;
        Ok(ir::Expr::rvalue(
            ir::ExprKind::Block(statements, ret),
            ret.typ,
        ))
    }

    pub fn monomorphize_lit(
        &mut self,
        ret: &ast::Lit<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let (lit, ty) = match ret {
            &ast::Lit::Bool(v) => (ir::Lit::Bool(v), ir::Ty::Builtin(ast::BuiltinType::Bool)),
            &ast::Lit::Null => {
                let ty = match type_hint {
                    Some(ir::Ty::Pointer(inner)) => ir::Ty::Pointer(inner),
                    _ => ir::Ty::Pointer(builtin!(self, Void)),
                };

                (ir::Lit::Null, ty)
            }
            &ast::Lit::Int(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => ir::Ty::Builtin(t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_integer() => ir::Ty::Builtin(*k),
                    _ => ir::Ty::Builtin(BuiltinType::I32),
                };

                (ir::Lit::Int(v), ty)
            }
            &ast::Lit::Float(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => ir::Ty::Builtin(t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_float() => ir::Ty::Builtin(*k),
                    _ => ir::Ty::Builtin(BuiltinType::I32),
                };

                (ir::Lit::Float(v.alloc_on(self.mono_ctx.ir)), ty)
            }
            _ => unimplemented!(),
        };

        Ok(ir::Expr::rvalue(
            ir::ExprKind::Lit(lit),
            self.mono_ctx.ir.intern_type(ty),
        ))
    }

    pub fn monomorphize_deref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let inner = self.monomorphize_expr(
            inner,
            type_hint.map(|ty| self.mono_ctx.ir.intern_type(ir::Ty::Pointer(ty))),
        )?;

        match inner.typ {
            ir::Ty::Pointer(ty) => Ok(ir::Expr::lvalue(ir::ExprKind::Deref(inner), ty)),
            _ => Err(AluminaError::TypeMismatch),
        }
    }

    pub fn monomorphize_ref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let type_hint = match type_hint {
            Some(ir::Ty::Pointer(inner)) => Some(*inner),
            _ => None,
        };

        let inner = self.monomorphize_expr(inner, type_hint)?;

        match inner.value_type {
            ir::ValueType::LValue => Ok(ir::Expr::rvalue(
                ir::ExprKind::Ref(inner),
                self.mono_ctx.ir.intern_type(ir::Ty::Pointer(inner.typ)),
            )),
            _ => Err(AluminaError::CannotAddressRValue),
        }
    }

    pub fn monomorphize_local(
        &mut self,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let id = self.mono_ctx.map_id(id);
        let typ = self
            .slot_types
            .get(&id)
            .copied()
            .expect("local with unknown type");

        Ok(ir::Expr::lvalue(ir::ExprKind::Local(id), typ))
    }

    pub fn monomorphize_unary(
        &mut self,
        op: ast::UnOp,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let inner = self.monomorphize_expr(inner, type_hint)?;

        match (op, inner.typ) {
            (ast::UnOp::Not, ir::Ty::Builtin(BuiltinType::Bool)) => {}
            (ast::UnOp::BitNot, ir::Ty::Builtin(b)) if b.is_integer() => {}
            (ast::UnOp::Neg, ir::Ty::Builtin(b)) if b.is_integer() || b.is_float() => {}
            _ => return Err(AluminaError::TypeMismatch),
        };

        Ok(ir::Expr::rvalue(ir::ExprKind::Unary(op, inner), inner.typ))
    }

    pub fn monomorphize_binary(
        &mut self,
        lhs: &ast::ExprP<'ast>,
        op: ast::BinOp,
        rhs: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let lhs = self.monomorphize_expr(
            lhs,
            match op {
                Eq | Neq | GEq | LEq | Lt | Gt => None,
                And | Or => Some(builtin!(self, Bool)),
                _ => type_hint,
            },
        )?;

        let rhs = self.monomorphize_expr(
            rhs,
            match op {
                Plus | Minus => match lhs.typ {
                    Pointer(_) => Some(builtin!(self, ISize)),
                    _ => Some(lhs.typ),
                },
                LShift | RShift => Some(builtin!(self, USize)),
                _ => Some(lhs.typ),
            },
        )?;

        let result_typ = match (lhs.typ, op, rhs.typ) {
            // Integer builtin types
            (
                Builtin(l),
                BitAnd | BitAnd | BitOr | BitXor | Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus
                | Mul | Div | Mod,
                Builtin(r),
            ) if l == r && l.is_integer() => {
                if op.is_comparison() {
                    Builtin(BuiltinType::Bool)
                } else {
                    *lhs.typ
                }
            }

            // Float builting types
            (Builtin(l), Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus | Mul | Div, Builtin(r))
                if l == r && l.is_float() =>
            {
                if op.is_comparison() {
                    Builtin(BuiltinType::Bool)
                } else {
                    *lhs.typ
                }
            }

            // Logical operators
            (
                Builtin(BuiltinType::Bool),
                And | Or | BitXor | Eq | Neq,
                Builtin(BuiltinType::Bool),
            ) => Builtin(BuiltinType::Bool),

            // Pointer comparison and pointer difference
            (Pointer(l), Eq | Neq | Lt | LEq | Gt | GEq | Minus, Pointer(r)) if l == r => {
                if op.is_comparison() {
                    Builtin(BuiltinType::Bool)
                } else {
                    *lhs.typ
                }
            }

            // Pointer arithmetic
            (Pointer(l), Plus | Minus, Builtin(BuiltinType::ISize)) => *lhs.typ,

            _ => return Err(AluminaError::InvalidBinOp(op)),
        };

        Ok(ir::Expr::rvalue(
            ir::ExprKind::Binary(lhs, op, rhs),
            self.mono_ctx.ir.intern_type(result_typ),
        ))
    }

    pub fn monomorphize_assign(
        &mut self,
        inner: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let lhs = self.monomorphize_expr(inner, None)?;
        let rhs = self.monomorphize_expr(rhs, Some(lhs.typ))?;

        if lhs.value_type != ir::ValueType::LValue {
            return Err(AluminaError::CannotAssignToRValue);
        }

        Ok(ir::Expr::rvalue(
            ir::ExprKind::Assign(lhs, rhs),
            builtin!(self, Void),
        ))
    }

    pub fn monomorphize_if(
        &mut self,
        cond: ast::ExprP<'ast>,
        then: ast::ExprP<'ast>,
        els: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let cond = self.monomorphize_expr(cond, Some(builtin!(self, Bool)))?;
        let then = self.monomorphize_expr(then, type_hint)?;
        let els = self.monomorphize_expr(els, Some(then.typ))?;

        if cond.typ != builtin!(self, Bool) {
            return Err(AluminaError::TypeMismatch);
        }

        if then.typ != els.typ {
            return Err(AluminaError::TypeMismatch);
        }

        Ok(ir::Expr::rvalue(
            ir::ExprKind::If(cond, then, els),
            then.typ,
        ))
    }

    pub fn monomorphize_tuple(
        &mut self,
        exprs: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let type_hints: Vec<_> = match type_hint {
            Some(ir::Ty::Tuple(elems)) if elems.len() == exprs.len() => {
                elems.iter().map(|t| Some(*t)).collect()
            }
            _ => repeat(None).take(exprs.len()).collect(),
        };

        let exprs = exprs
            .iter()
            .zip(type_hints.into_iter())
            .map(|(e, t)| self.monomorphize_expr(e, t))
            .collect::<Result<Vec<_>, _>>()?;

        let element_types: Vec<_> = exprs.iter().map(|e| e.typ).collect();
        let tuple_type = self
            .mono_ctx
            .ir
            .intern_type(ir::Ty::Tuple(element_types.alloc_on(self.mono_ctx.ir)));

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.builder.local(temporary, tuple_type);

        let statements = once(ir::Statement::LocalDef(temporary, tuple_type))
            .chain(exprs.into_iter().enumerate().map(|(i, e)| {
                ir::Statement::Expression(
                    self.builder
                        .assign(self.builder.tuple_index(local, i, e.typ), e),
                )
            }))
            .collect::<Vec<_>>()
            .alloc_on(self.mono_ctx.ir);

        Ok(ir::Expr::rvalue(
            ir::ExprKind::Block(statements, local),
            tuple_type,
        ))
    }

    pub fn monomorphize_cast(
        &mut self,
        expr: ast::ExprP<'ast>,
        target_type: ast::TyP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::Expr<'ir>, AluminaError> {
        let expr = self.monomorphize_expr(expr, None)?;
        let typ = self.monomorphize_type(target_type)?;

        match (expr.typ, typ) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}

            // Pointer casts
            (ir::Ty::Pointer(_), ir::Ty::Pointer(_)) => {}
            (ir::Ty::Builtin(BuiltinType::USize), ir::Ty::Pointer(_)) => {}
            (ir::Ty::Pointer(_), ir::Ty::Builtin(BuiltinType::USize)) => {}

            _ => return Err(AluminaError::InvalidCast),
        }

        Ok(ir::Expr::rvalue(ir::ExprKind::Cast(expr, typ), typ))
    }

    pub fn monomorphize_expr(
        &mut self,
        expr: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        println!("monomorphize_expr {:?}", expr);
        let result = match expr {
            ast::Expr::Void => ir::Expr::rvalue(
                ir::ExprKind::Void,
                self.mono_ctx
                    .ir
                    .intern_type(ir::Ty::Builtin(ast::BuiltinType::Void)),
            ),
            ast::Expr::Block(statements, ret) => {
                self.monomorphize_block(statements, ret, type_hint)?
            }
            ast::Expr::Lit(lit) => self.monomorphize_lit(lit, type_hint)?,
            ast::Expr::Deref(expr) => self.monomorphize_deref(expr, type_hint)?,
            ast::Expr::Ref(expr) => self.monomorphize_ref(expr, type_hint)?,
            ast::Expr::Local(id) => self.monomorphize_local(*id, type_hint)?,
            ast::Expr::Unary(op, inner) => self.monomorphize_unary(*op, inner, type_hint)?,
            ast::Expr::Assign(lhs, rhs) => self.monomorphize_assign(lhs, rhs, type_hint)?,
            ast::Expr::If(cond, then, els) => self.monomorphize_if(cond, then, els, type_hint)?,
            ast::Expr::Cast(expr, typ) => self.monomorphize_cast(expr, typ, type_hint)?,
            ast::Expr::Binary(lhs, op, rhs) => {
                self.monomorphize_binary(lhs, *op, rhs, type_hint)?
            }
            ast::Expr::Tuple(exprs) => self.monomorphize_tuple(exprs, type_hint)?,
            _ => panic!("unimplemented {:?}", expr),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }
}
