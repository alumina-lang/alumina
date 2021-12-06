use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;
use std::iter::{once, repeat};

use once_cell::sync::{Lazy, OnceCell};

use super::IrCtx;
use crate::ast::{expressions, BuiltinType};
use crate::common::ArenaAllocatable;
use crate::ir::{FuncBodyCell, ValueType};
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

    fn fill_block(
        &self,
        target: &mut Vec<ir::Statement<'ir>>,
        iter: impl IntoIterator<Item = ir::Statement<'ir>>,
    ) -> Result<(), ir::ExprP<'ir>> {
        use ir::Expr;
        use ir::ExprKind::*;
        use ir::Statement::*;

        for stmt in iter {
            match stmt {
                Expression(expr) if expr.diverges() => return Err(expr),
                Expression(Expr {
                    kind: Block(stmts, ret),
                    ..
                }) => {
                    self.fill_block(target, stmts.into_iter().cloned())?;
                    target.push(Expression(ret))
                }
                Expression(expr) if expr.pure() => {}
                _ => target.push(stmt),
            }
        }

        Ok(())
    }

    pub fn block(
        &self,
        statements: impl IntoIterator<Item = ir::Statement<'ir>>,
        ret: ir::ExprP<'ir>,
    ) -> ir::ExprP<'ir> {
        let mut merged = Vec::new();

        let ret = match self.fill_block(&mut merged, statements.into_iter()) {
            Ok(()) => ret,
            Err(expr) => expr,
        };

        if merged.is_empty() {
            return ret;
        }

        ir::Expr::rvalue(ir::ExprKind::Block(merged.alloc_on(self.ir), ret), ret.typ)
            .alloc_on(self.ir)
    }

    pub fn diverges(&self, exprs: impl IntoIterator<Item = ir::ExprP<'ir>>) -> ir::ExprP<'ir> {
        let block = self.block(
            exprs
                .into_iter()
                .map(|expr| ir::Statement::Expression(expr)),
            self.void(),
        );

        // This is a bit of hack, helper function for blocks that diverge. To simplify the caller's code,
        // we accept any block (can contain excess) and if it doesn't actually diverge, we panic here.
        assert!(block.diverges());

        block
    }

    pub fn assign(&self, lhs: ir::ExprP<'ir>, rhs: ir::ExprP<'ir>) -> ir::ExprP<'ir> {
        ir::Expr::rvalue(
            ir::ExprKind::Assign(lhs, rhs),
            self.ir.intern_type(ir::Ty::Builtin(BuiltinType::Void)),
        )
        .alloc_on(self.ir)
    }

    pub fn void(&self) -> ir::ExprP<'ir> {
        ir::Expr::rvalue(
            ir::ExprKind::Void,
            self.ir.intern_type(ir::Ty::Builtin(BuiltinType::Void)),
        )
        .alloc_on(self.ir)
    }

    pub fn unreachable(&self) -> ir::ExprP<'ir> {
        ir::Expr::rvalue(
            ir::ExprKind::Unreachable,
            self.ir.intern_type(ir::Ty::Builtin(BuiltinType::Never)),
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
            is_const: tuple.is_const,
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

type ReverseMap<'ast, 'ir> = HashMap<ir::IRItemP<'ir>, MonomorphizeKey<'ast, 'ir>>;

struct TypeInferer<'a, 'ast, 'ir> {
    mono_ctx: &'a MonoCtx<'ast, 'ir>,
    placeholders: Vec<ast::AstId>,
    source: Vec<ast::TyP<'ast>>,
    target: Vec<ir::TyP<'ir>>,
    reverse_map: OnceCell<ReverseMap<'ast, 'ir>>,
}

impl<'a, 'ast, 'ir> TypeInferer<'a, 'ast, 'ir> {
    fn new(
        mono_ctx: &'a MonoCtx<'ast, 'ir>,
        placeholders: Vec<ast::AstId>,
        source: Vec<ast::TyP<'ast>>,
        target: Vec<ir::TyP<'ir>>,
    ) -> Self {
        TypeInferer {
            mono_ctx,
            placeholders,
            source,
            target,
            reverse_map: OnceCell::new(),
        }
    }

    fn match_slot(
        &self,
        inferred: &mut HashMap<ast::AstId, ir::TyP<'ir>>,
        src: ast::TyP<'ast>,
        tgt: ir::TyP<'ir>,
    ) -> Result<(), ()> {
        println!("match_slot: {:?} {:?}", src, tgt);
        match (src, tgt) {
            (ast::Ty::Extern(_), _) | (ast::Ty::NamedType(_), _) | (ast::Ty::Builtin(_), _) => {
                // those do not participate in inference
            }
            (ast::Ty::Placeholder(id), _) => {
                inferred.insert(*id, tgt);
                if inferred.len() == self.placeholders.len() {
                    return Err(());
                }
            }
            (ast::Ty::Pointer(a1, a2), ir::Ty::Pointer(b1, b2)) => {
                if a2 != b2 {
                    return Err(());
                }
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Array(a1, a2), ir::Ty::Array(b1, b2)) => {
                if a2 != b2 {
                    return Err(());
                }
                self.match_slot(inferred, a1, b1)?;
            }
            (ast::Ty::Slice(a), ir::Ty::Slice(b)) => self.match_slot(inferred, a, b)?,
            (ast::Ty::Tuple(a), ir::Ty::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(());
                }
                for (a, b) in a.iter().zip(b.iter()) {
                    self.match_slot(inferred, a, b)?;
                }
            }
            (ast::Ty::Function(a1, a2), ir::Ty::Function(b1, b2)) => {
                for (a, b) in a1.iter().zip(b1.iter()) {
                    self.match_slot(inferred, a, b)?;
                }
                self.match_slot(inferred, a2, b2)?;
            }
            (ast::Ty::GenericType(item, holders), ir::Ty::NamedType(t)) => {
                let reverse_map: &_ = self.reverse_map.get_or_init(|| {
                    self.mono_ctx
                        .finished
                        .iter()
                        .map(|(a, &b)| (b, a.clone()))
                        .collect()
                });

                let mono_key = reverse_map.get(t).unwrap();
                if mono_key.0 != *item {
                    return Err(());
                }

                for (holder, t) in holders.iter().zip(mono_key.1.iter()) {
                    self.match_slot(inferred, *holder, *t)?;
                }
            }
            _ => return Err(()),
        }

        Ok(())
    }

    pub fn try_infer(&mut self) -> Option<Vec<ir::TyP<'ir>>> {
        println!("try_infer: {:?} {:?}", self.source, self.target);
        if self.source.len() != self.target.len() {
            return None;
        }

        let mut inferred = HashMap::new();

        for (param, actual) in self.source.iter().zip(self.target.iter()) {
            if self.match_slot(&mut inferred, param, *actual).is_err() {
                break;
            }
        }

        if inferred.len() == self.placeholders.len() {
            Some(self.placeholders.iter().map(|id| inferred[id]).collect())
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopContext<'ir> {
    type_hint: Option<ir::TyP<'ir>>,
    loop_result: ir::IrId,

    break_label: ir::IrId,
    continue_label: ir::IrId,
}

pub struct Monomorphizer<'a, 'ast, 'ir> {
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    slot_types: HashMap<ir::IrId, ir::TyP<'ir>>,
    builder: ExpressionBuilder<'ir>,
    loop_contexts: Vec<LoopContext<'ir>>,
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
            loop_contexts: Vec::new(),
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
            loop_contexts: Vec::new(),
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
                    .args
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
                    args: &parameters.alloc_on(child.mono_ctx.ir),
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

                if !return_type.assignable_from(body.typ) {
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
            ast::Ty::Pointer(inner, is_const) => {
                ir::Ty::Pointer(self.monomorphize_type(inner)?, is_const)
            }
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
                        match type_hint {
                            Some(ty) if !ty.assignable_from(init.typ) => {
                                return Err(AluminaError::TypeMismatch);
                            }
                            _ => {}
                        };

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
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let statements = statements
            .iter()
            .map(|stmt| self.monomorphize_stmt(stmt))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        let ret = self.monomorphize_expr(ret, type_hint)?;

        Ok(self.builder.block(statements, ret))
    }

    pub fn monomorphize_lit(
        &mut self,
        ret: &ast::Lit<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let (lit, ty) = match ret {
            &ast::Lit::Bool(v) => (ir::Lit::Bool(v), ir::Ty::Builtin(ast::BuiltinType::Bool)),
            &ast::Lit::Null => {
                let ty = match type_hint {
                    Some(ir::Ty::Pointer(inner, _)) => ir::Ty::Pointer(inner, true),
                    _ => ir::Ty::Pointer(builtin!(self, Void), true),
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

        Ok(
            ir::Expr::rvalue(ir::ExprKind::Lit(lit), self.mono_ctx.ir.intern_type(ty))
                .alloc_on(self.mono_ctx.ir),
        )
    }

    pub fn monomorphize_deref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.monomorphize_expr(
            inner,
            type_hint.map(|ty| self.mono_ctx.ir.intern_type(ir::Ty::Pointer(ty, true))),
        )?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.typ {
            ir::Ty::Pointer(ty, false) => ir::Expr::lvalue(ir::ExprKind::Deref(inner), ty),
            ir::Ty::Pointer(ty, true) => ir::Expr::lvalue(ir::ExprKind::Deref(inner), ty),
            _ => return Err(AluminaError::TypeMismatch),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_ref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let type_hint = match type_hint {
            Some(ir::Ty::Pointer(inner, _)) => Some(*inner),
            _ => None,
        };

        let inner = self.monomorphize_expr(inner, type_hint)?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.value_type {
            ir::ValueType::LValue => ir::Expr::rvalue(
                ir::ExprKind::Ref(inner),
                self.mono_ctx
                    .ir
                    .intern_type(ir::Ty::Pointer(inner.typ, inner.is_const)),
            ),
            _ => return Err(AluminaError::CannotAddressRValue),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_local(
        &mut self,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let id = self.mono_ctx.map_id(id);
        let typ = self
            .slot_types
            .get(&id)
            .copied()
            .expect("local with unknown type");

        Ok(self.builder.local(id, typ))
    }

    pub fn monomorphize_unary(
        &mut self,
        op: ast::UnOp,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.monomorphize_expr(inner, type_hint)?;
        if inner.diverges() {
            return Ok(inner);
        }

        match (op, inner.typ) {
            (ast::UnOp::Not, ir::Ty::Builtin(BuiltinType::Bool)) => {}
            (ast::UnOp::BitNot, ir::Ty::Builtin(b)) if b.is_integer() => {}
            (ast::UnOp::Neg, ir::Ty::Builtin(b)) if b.is_integer() || b.is_float() => {}
            _ => return Err(AluminaError::TypeMismatch),
        };

        let result = ir::Expr::rvalue(ir::ExprKind::Unary(op, inner), inner.typ);

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_binary(
        &mut self,
        lhs: &ast::ExprP<'ast>,
        op: ast::BinOp,
        rhs: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
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
                    Pointer(_, _) => Some(builtin!(self, ISize)),
                    _ => Some(lhs.typ),
                },
                LShift | RShift => Some(builtin!(self, USize)),
                _ => Some(lhs.typ),
            },
        )?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

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
            (Pointer(l, _), Eq | Neq | Lt | LEq | Gt | GEq, Pointer(r, _)) if l == r => {
                Builtin(BuiltinType::Bool)
            }

            (Pointer(l, l_const), Minus, Pointer(r, r_const)) if l == r && l_const == r_const => {
                *lhs.typ
            }

            // Pointer arithmetic
            (Pointer(l, _), Plus | Minus, Builtin(BuiltinType::ISize)) => *lhs.typ,

            _ => return Err(AluminaError::InvalidBinOp(op)),
        };

        let result = ir::Expr::rvalue(
            ir::ExprKind::Binary(lhs, op, rhs),
            self.mono_ctx.ir.intern_type(result_typ),
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_assign(
        &mut self,
        inner: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let lhs = self.monomorphize_expr(inner, None)?;
        let rhs = self.monomorphize_expr(rhs, Some(lhs.typ))?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.builder.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(AluminaError::CannotAssignToRValue);
        }

        if lhs.is_const {
            return Err(AluminaError::CannotAssignToConst);
        }

        if !lhs.typ.assignable_from(rhs.typ) {
            return Err(AluminaError::TypeMismatch);
        }

        Ok(self.builder.assign(lhs, rhs))
    }

    pub fn monomorphize_if(
        &mut self,
        cond: ast::ExprP<'ast>,
        then: ast::ExprP<'ast>,
        els: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let cond = self.monomorphize_expr(cond, Some(builtin!(self, Bool)))?;
        if cond.diverges() {
            return Ok(cond);
        }

        let then = self.monomorphize_expr(then, type_hint)?;
        let els = self.monomorphize_expr(els, Some(then.typ))?;

        if builtin!(self, Bool).assignable_from(cond.typ) {
            return Err(AluminaError::TypeMismatch);
        }

        let gcd = ir::Ty::gcd(then.typ, els.typ);
        if !gcd.assignable_from(then.typ) || !gcd.assignable_from(els.typ) {
            return Err(AluminaError::TypeMismatch);
        }

        let result = ir::Expr::rvalue(
            ir::ExprKind::If(cond, then, els),
            self.mono_ctx.ir.intern_type(gcd),
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_tuple(
        &mut self,
        exprs: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let type_hints: Vec<_> = match type_hint {
            Some(ir::Ty::Tuple(elems)) if elems.len() == exprs.len() => {
                elems.iter().map(|t| Some(*t)).collect()
            }
            _ => repeat(None).take(exprs.len()).collect(),
        };

        let lowered = exprs
            .iter()
            .zip(type_hints.into_iter())
            .map(|(expr, hint)| self.monomorphize_expr(expr, hint))
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(lowered));
        }

        let element_types: Vec<_> = lowered.iter().map(|e| e.typ).collect();
        let tuple_type = self
            .mono_ctx
            .ir
            .intern_type(ir::Ty::Tuple(element_types.alloc_on(self.mono_ctx.ir)));

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.builder.local(temporary, tuple_type);

        let statements = once(ir::Statement::LocalDef(temporary, tuple_type))
            .chain(lowered.into_iter().enumerate().map(|(i, e)| {
                ir::Statement::Expression(
                    self.builder
                        .assign(self.builder.tuple_index(local, i, e.typ), e),
                )
            }))
            .collect::<Vec<_>>();

        Ok(self.builder.block(statements, local))
    }

    pub fn monomorphize_cast(
        &mut self,
        expr: ast::ExprP<'ast>,
        target_type: ast::TyP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let expr = self.monomorphize_expr(expr, None)?;
        if expr.diverges() {
            return Ok(expr);
        }

        let typ = self.monomorphize_type(target_type)?;

        match (expr.typ, typ) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}

            // Pointer casts
            (ir::Ty::Pointer(_, _), ir::Ty::Pointer(_, _)) => {}
            (ir::Ty::Builtin(BuiltinType::USize), ir::Ty::Pointer(_, _)) => {}
            (ir::Ty::Pointer(_, _), ir::Ty::Builtin(BuiltinType::USize)) => {}

            _ => return Err(AluminaError::InvalidCast),
        }

        let result = ir::Expr::rvalue(ir::ExprKind::Cast(expr, typ), typ);

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_loop(
        &mut self,
        body: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_result = self.mono_ctx.ir.make_id();
        let break_label = self.mono_ctx.ir.make_id();
        let continue_label = self.mono_ctx.ir.make_id();

        self.loop_contexts.push(LoopContext {
            loop_result,
            type_hint,
            break_label,
            continue_label,
        });

        let body = self.monomorphize_expr(body, None);
        self.loop_contexts.pop();

        let body = body?;
        if body.diverges() {
            return Ok(body);
        }

        self.loop_contexts.pop();

        let mut statements = vec![
            ir::Statement::Label(continue_label),
            ir::Statement::Expression(body),
            ir::Statement::Goto(continue_label),
            ir::Statement::Label(break_label),
        ];

        let result = match self.slot_types.get(&loop_result) {
            None => self.builder.block(statements, self.builder.unreachable()),
            Some(typ) => {
                statements.insert(0, ir::Statement::LocalDef(loop_result, *typ));
                self.builder
                    .block(statements, self.builder.local(loop_result, *typ))
            }
        };

        Ok(result)
    }

    pub fn monomorphize_break(
        &mut self,
        expr: Option<ast::ExprP<'ast>>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self
            .loop_contexts
            .last()
            .expect("break outside of loop")
            .clone();

        let expr = expr
            .map(|e| self.monomorphize_expr(e, loop_context.type_hint))
            .transpose()?;

        if expr.map(|e| e.diverges()).unwrap_or(false) {
            return Ok(expr.unwrap());
        }

        let break_typ = expr.map(|e| e.typ).unwrap_or(builtin!(self, Void));
        let slot_type = match self.slot_types.entry(loop_context.loop_result) {
            Entry::Vacant(v) => {
                v.insert(break_typ);
                break_typ
            }
            Entry::Occupied(o) => o.get(),
        };

        if !slot_type.assignable_from(break_typ) {
            return Err(AluminaError::TypeMismatch);
        }

        let statements = [
            ir::Statement::Expression(self.builder.assign(
                self.builder.local(loop_context.loop_result, slot_type),
                expr.unwrap_or(self.builder.void()),
            )),
            ir::Statement::Goto(loop_context.break_label),
        ];

        Ok(self.builder.block(statements, self.builder.unreachable()))
    }

    pub fn monomorphize_continue(
        &mut self,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self.loop_contexts.last().expect("continue outside of loop");

        let statements = [ir::Statement::Goto(loop_context.continue_label)];

        Ok(self.builder.block(statements, self.builder.unreachable()))
    }

    pub fn monomorphize_call(
        &mut self,
        callee: ast::ExprP<'ast>,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // Function calls are not completely referentially tranparent, as we do not support
        // pointers-to-method, so these need to be invoked directly. This allow us to switch on the
        // callee's expression kind to determine how to handle it.

        let callee = match callee {
            ast::Expr::Fn(item) => match item.get() {
                ast::Item::Function(fun) => {
                    if fun.placeholders.is_empty() {
                        self.monomorphize(item)?
                    } else {
                        let target_args = args
                            .iter()
                            .map(|arg| self.monomorphize_expr(arg, None).map(|e| e.typ))
                            .collect::<Result<Vec<_>, _>>();

                        if let Ok(mut target_args) = target_args {
                            let mut source_args: Vec<_> = fun.args.iter().map(|p| p.ty).collect();

                            match type_hint {
                                Some(typ) => {
                                    source_args.push(fun.return_type);
                                    target_args.push(typ);
                                }
                                None => {}
                            }

                            let mut type_inferer = TypeInferer::new(
                                self.mono_ctx,
                                fun.placeholders.into(),
                                source_args,
                                target_args,
                            );

                            if let Some(replacements) = type_inferer.try_infer() {
                                self.monomorphize_item(MonomorphizeKey(
                                    item,
                                    replacements.alloc_on(self.mono_ctx.ir),
                                ))?
                            } else {
                                return Err(AluminaError::TypeHintRequired);
                            }
                        } else {
                            return Err(AluminaError::TypeHintRequired);
                        }
                    }
                }
                _ => panic!("expected function here"),
            },
            _ => unimplemented!(),
        };

        let func = match callee.get() {
            ir::IRItem::Function(func) => func,
            _ => unreachable!(),
        };

        let callee =
            ir::Expr::rvalue(ir::ExprKind::Fn(callee), func.return_type).alloc_on(self.mono_ctx.ir);

        if func.args.len() != args.len() {
            return Err(AluminaError::ParamCountMismatch(
                func.args.len(),
                args.len(),
            ));
        }

        let args = args
            .iter()
            .zip(func.args)
            .map(|(arg, param)| self.monomorphize_expr(arg, Some(param.ty)))
            .collect::<Result<Vec<_>, _>>()?;

        if callee.diverges() || args.iter().any(|e| e.diverges()) {
            return Ok(self.builder.diverges(once(callee).chain(args)));
        }

        for (arg, param) in args.iter().zip(func.args) {
            if !arg.typ.assignable_from(param.ty) {
                return Err(AluminaError::TypeMismatch);
            }
        }

        let result = ir::Expr::rvalue(
            ir::ExprKind::Call(callee, args.alloc_on(self.mono_ctx.ir)),
            func.return_type,
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_fn(
        &mut self,
        item: ast::ItemP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item = self.monomorphize(item)?;
        let func = match item.get() {
            ir::IRItem::Function(item) => item,
            _ => panic!("expected function here"),
        };

        let fn_type = ir::Ty::Function(
            func.args
                .iter()
                .map(|a| a.ty)
                .collect::<Vec<_>>()
                .alloc_on(self.mono_ctx.ir),
            func.return_type,
        );

        let result = ir::Expr::rvalue(
            ir::ExprKind::Fn(item),
            self.mono_ctx.ir.intern_type(fn_type),
        );

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    pub fn monomorphize_tuple_index(
        &mut self,
        tup: ast::ExprP<'ast>,
        index: usize,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let tup = self.monomorphize_expr(tup, None)?;
        if tup.diverges() {
            return Ok(tup);
        }

        let result = match tup.typ {
            ir::Ty::Tuple(types) => {
                if types.len() <= index {
                    return Err(AluminaError::TupleIndexOutOfBounds);
                }
                self.builder.tuple_index(tup, index, types[index])
            }
            _ => return Err(AluminaError::TypeMismatch),
        };

        Ok(result)
    }

    pub fn monomorphize_expr(
        &mut self,
        expr: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        println!("monomorphize_expr {:?}", expr);
        let result = match expr {
            ast::Expr::Void => Ok(self.builder.void()),
            ast::Expr::Block(statements, ret) => {
                self.monomorphize_block(statements, ret, type_hint)
            }
            ast::Expr::Lit(lit) => self.monomorphize_lit(lit, type_hint),
            ast::Expr::Deref(expr) => self.monomorphize_deref(expr, type_hint),
            ast::Expr::Ref(expr) => self.monomorphize_ref(expr, type_hint),
            ast::Expr::Local(id) => self.monomorphize_local(*id, type_hint),
            ast::Expr::Unary(op, inner) => self.monomorphize_unary(*op, inner, type_hint),
            ast::Expr::Assign(lhs, rhs) => self.monomorphize_assign(lhs, rhs, type_hint),
            ast::Expr::If(cond, then, els) => self.monomorphize_if(cond, then, els, type_hint),
            ast::Expr::Cast(expr, typ) => self.monomorphize_cast(expr, typ, type_hint),
            ast::Expr::Loop(body) => self.monomorphize_loop(body, type_hint),
            ast::Expr::Binary(lhs, op, rhs) => self.monomorphize_binary(lhs, *op, rhs, type_hint),
            ast::Expr::Break(value) => self.monomorphize_break(*value, type_hint),
            ast::Expr::Continue => self.monomorphize_continue(type_hint),
            ast::Expr::Tuple(exprs) => self.monomorphize_tuple(exprs, type_hint),
            ast::Expr::TupleIndex(tup, index) => {
                self.monomorphize_tuple_index(tup, *index, type_hint)
            }
            ast::Expr::Call(func, args) => self.monomorphize_call(func, args, type_hint),
            ast::Expr::Fn(item) => self.monomorphize_fn(item, type_hint),
            _ => panic!("unimplemented {:?}", expr),
        };

        let result = match result {
            Ok(result) => result,
            Err(e) => panic!("{} at {:?}", e, expr),
        };

        Ok(result)
    }
}
