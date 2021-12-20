use core::panic;

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use std::iter::{once, repeat};

use indexmap::IndexMap;
use once_cell::unsync::OnceCell;

use super::builder::{ExpressionBuilder, TypeBuilder};
use super::const_eval::{const_eval, numeric_of_kind, Value};
use super::elide_zst::ZstElider;
use super::infer::TypeInferer;
use super::lang::LangTypeKind;
use super::{FuncBody, IRItemP, Lit, LocalDef, UnqualifiedKind};
use crate::ast::lang::{LangItemKind, LangItemMap};
use crate::ast::{Attribute, BuiltinType, Parameter};
use crate::common::{
    AluminaError, ArenaAllocatable, CodeError, CodeErrorBacktrace, CodeErrorBuilder, Marker,
};
use crate::diagnostics::DiagnosticContext;
use crate::intrinsics::CompilerIntrinsics;
use crate::ir::ValueType;
use crate::{ast, common::CodeErrorKind, ir};

macro_rules! mismatch {
    ($expected:expr, $actual:expr) => {
        crate::common::CodeErrorKind::TypeMismatch(
            format!("{:?}", $expected),
            format!("{:?}", $actual),
        )
    };
}

pub struct MonoCtx<'ast, 'ir> {
    ir: &'ir ir::IrCtx<'ir>,
    diag_ctx: DiagnosticContext,
    id_map: HashMap<ast::AstId, ir::IrId>,
    lang_items: LangItemMap<'ast>,
    finished: IndexMap<MonomorphizeKey<'ast, 'ir>, ir::IRItemP<'ir>>,
    reverse_map: HashMap<ir::IRItemP<'ir>, MonomorphizeKey<'ast, 'ir>>,
    intrinsics: CompilerIntrinsics<'ir>,
    static_local_defs: HashMap<ir::IRItemP<'ir>, Vec<LocalDef<'ir>>>,
    extra_items: Vec<IRItemP<'ir>>,
}
enum BoundCheckResult {
    Matches,
    DoesNotMatch,
    DoesNotMatchBecause(String),
}

impl<'ast, 'ir> MonoCtx<'ast, 'ir> {
    pub fn new(
        ir: &'ir ir::IrCtx<'ir>,
        diag_ctx: DiagnosticContext,
        lang_items: LangItemMap<'ast>,
    ) -> Self {
        MonoCtx {
            ir,
            diag_ctx,
            id_map: HashMap::new(),
            finished: IndexMap::new(),
            reverse_map: HashMap::new(),
            lang_items,
            intrinsics: CompilerIntrinsics::new(ir),
            extra_items: Vec::new(),
            static_local_defs: HashMap::new(),
        }
    }

    fn map_id(&mut self, id: ast::AstId) -> ir::IrId {
        *self.id_map.entry(id).or_insert_with(|| self.ir.make_id())
    }

    pub fn reverse_lookup(&self, item: ir::IRItemP<'ir>) -> MonomorphizeKey<'ast, 'ir> {
        self.reverse_map
            .get(&item)
            .cloned()
            .expect("reverse lookup failed")
    }

    pub fn get_lang_type_kind(&self, typ: ir::TyP<'ir>) -> Option<LangTypeKind<'ir>> {
        let item = match typ {
            ir::Ty::NamedType(item) => item,
            _ => return None,
        };

        let item = self.reverse_lookup(item);
        if self.lang_items.get(LangItemKind::Slice).ok() == Some(item.0) {
            return Some(LangTypeKind::Slice(item.1[0]));
        }

        if self.lang_items.get(LangItemKind::DynPtr).ok() == Some(item.0) {
            return Some(LangTypeKind::Dyn(item.1[0]));
        }

        return None;
    }

    pub fn into_inner(self) -> Vec<ir::IRItemP<'ir>> {
        self.finished
            .values()
            .copied()
            .chain(self.extra_items)
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct LoopContext<'ir> {
    type_hint: Option<ir::TyP<'ir>>,
    loop_result: ir::IrId,
    break_label: ir::IrId,
    continue_label: ir::IrId,
}

#[derive(Debug, Clone)]
pub struct DeferContext<'ir> {
    defered: Vec<(ir::IrId, ir::ExprP<'ir>)>,
    in_defer: bool,
    return_label: ir::IrId,
    return_local: ir::IrId,
}

impl DeferContext<'_> {
    fn new(return_label: ir::IrId, return_local: ir::IrId) -> Self {
        DeferContext {
            defered: Vec::new(),
            in_defer: false,
            return_label,
            return_local,
        }
    }
}

pub struct Monomorphizer<'a, 'ast, 'ir> {
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    exprs: ExpressionBuilder<'ir>,
    types: TypeBuilder<'ir>,

    replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    return_type: Option<ir::TyP<'ir>>,
    loop_contexts: Vec<LoopContext<'ir>>,
    local_types: HashMap<ir::IrId, ir::TyP<'ir>>,
    local_defs: Vec<ir::LocalDef<'ir>>,
    defer_context: Option<DeferContext<'ir>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphizeKey<'ast, 'ir>(pub ast::ItemP<'ast>, pub &'ir [ir::TyP<'ir>]);

impl<'a, 'ast, 'ir> Monomorphizer<'a, 'ast, 'ir> {
    pub fn new<'b>(mono_ctx: &'b mut MonoCtx<'ast, 'ir>) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        Monomorphizer {
            mono_ctx,
            replacements: HashMap::new(),
            local_types: HashMap::new(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: None,
            loop_contexts: Vec::new(),
            local_defs: Vec::new(),
            defer_context: None,
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
            local_types: HashMap::new(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: None,
            loop_contexts: Vec::new(),
            local_defs: Vec::new(),
            defer_context: None,
        }
    }

    pub fn monomorphize(
        &mut self,
        item: ast::ItemP<'ast>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        self.monomorphize_item(MonomorphizeKey(item, &[]))
    }

    fn monomorphize_enum(
        &mut self,
        item: ir::IRItemP<'ir>,
        en: &ast::Enum<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        if generic_args.len() != 0 {
            return Err(CodeErrorKind::GenericParamCountMismatch(
                0,
                generic_args.len(),
            ))
            .with_no_span();
        }

        let mut members = Vec::new();
        let mut child = Self::new(self.mono_ctx);
        let mut type_hint = None;
        let mut taken_values = HashSet::new();

        let (valued, non_valued): (Vec<_>, Vec<_>) =
            en.members.iter().copied().partition(|m| m.value.is_some());

        for m in valued {
            let expr = child.lower_expr(m.value.unwrap(), type_hint)?;
            let value = const_eval(expr)
                .map_err(|_| CodeErrorKind::CannotConstEvaluate)
                .with_span(m.value.unwrap().span)?;

            let value_type = match value.type_kind() {
                Some(ir::Ty::Builtin(b)) if b.is_integer() => self.types.builtin(b),
                _ => {
                    return Err(CodeErrorKind::InvalidValueForEnumVariant)
                        .with_span(m.value.unwrap().span)?
                }
            };

            if !type_hint
                .get_or_insert(value_type)
                .assignable_from(value_type)
            {
                return Err(mismatch!(type_hint.unwrap(), value_type)).with_span(m.span);
            }

            if !taken_values.insert(value) {
                return Err(CodeErrorKind::DuplicateEnumMember).with_span(m.span);
            }

            members.push(ir::EnumMember {
                id: child.mono_ctx.map_id(m.id),
                value: child.exprs.const_value(value),
            });
        }

        // This monstrosity to populate non-valued members with arbitrary types using
        // const-eval. It's bad, but it works.
        let kind = match type_hint.get_or_insert(child.types.builtin(BuiltinType::I32)) {
            ir::Ty::Builtin(k) => *k,
            _ => unreachable!(),
        };

        let mut counter = numeric_of_kind!(kind, 0);
        for m in non_valued {
            let next_non_taken = loop {
                if taken_values.insert(counter) {
                    break counter;
                }
                counter = const_eval(self.exprs.binary(
                    ast::BinOp::Plus,
                    self.exprs.const_value(counter),
                    self.exprs.const_value(numeric_of_kind!(kind, 1)),
                    type_hint.unwrap(),
                ))
                .unwrap();
            };

            members.push(ir::EnumMember {
                id: child.mono_ctx.map_id(m.id),
                value: self.exprs.const_value(next_non_taken),
            });
        }

        let res = ir::IRItem::Enum(ir::Enum {
            name: en.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            underlying_type: type_hint.unwrap(),
            members: members.alloc_on(child.mono_ctx.ir),
        });

        item.assign(res);

        Ok(())
    }

    fn monomorphize_struct(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::StructLike<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        if generic_args.len() != s.placeholders.len() {
            return Err(CodeErrorKind::GenericParamCountMismatch(
                s.placeholders.len(),
                generic_args.len(),
            ))
            .with_no_span();
        }

        let mut child = Self::with_replacements(
            self.mono_ctx,
            s.placeholders
                .iter()
                .zip(generic_args.iter())
                .map(|(&k, &v)| (k.id, v))
                .collect(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            for bound in placeholder.bounds {
                let bound = child.lower_type(bound)?;
                protocol_bounds.push((bound, ty.clone()));
            }
        }
        child.check_protocol_bounds(protocol_bounds)?;

        let fields = s
            .fields
            .iter()
            .map(|f| {
                Ok(ir::Field {
                    id: child.mono_ctx.map_id(f.id),
                    ty: child.lower_type(f.typ)?,
                })
            })
            .collect::<Result<Vec<_>, AluminaError>>()?;

        let res = ir::IRItem::StructLike(ir::StructLike {
            name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            fields: fields.alloc_on(self.mono_ctx.ir),
            is_union: s.is_union,
        });
        item.assign(res);

        Ok(())
    }

    fn monomorphize_protocol(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::Protocol<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        if generic_args.len() != s.placeholders.len() {
            return Err(CodeErrorKind::GenericParamCountMismatch(
                s.placeholders.len(),
                generic_args.len(),
            ))
            .with_no_span();
        }

        let mut child = Self::with_replacements(
            self.mono_ctx,
            s.placeholders
                .iter()
                .zip(generic_args.iter())
                .map(|(&k, &v)| (k.id, v))
                .collect(),
        );

        // Protocols can have their own protocol bounds, yay!
        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            for bound in placeholder.bounds {
                let bound = child.lower_type(bound)?;
                protocol_bounds.push((bound, ty.clone()));
            }
        }
        child.check_protocol_bounds(protocol_bounds)?;

        let mut methods = Vec::new();
        for m in s.methods {
            let mut param_types = Vec::new();
            for p in m.args {
                param_types.push(child.lower_type(p.typ)?);
            }
            let ret = child.lower_type(m.return_type)?;

            methods.push(ir::ProtocolFunction {
                name: m.name.alloc_on(child.mono_ctx.ir),
                arg_types: param_types.alloc_on(child.mono_ctx.ir),
                return_type: ret,
            });
        }

        let res = ir::IRItem::Protocol(ir::Protocol {
            name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            methods: methods.alloc_on(child.mono_ctx.ir),
        });
        item.assign(res);

        Ok(())
    }

    fn check_protocol_bounds(
        &mut self,
        bounds: Vec<(ir::TyP<'ir>, ir::TyP<'ir>)>,
    ) -> Result<(), AluminaError> {
        for (bound, ty) in bounds {
            match self.check_protocol_bound(bound, ty)? {
                BoundCheckResult::Matches => {}
                BoundCheckResult::DoesNotMatch => {
                    return Err(CodeErrorKind::ProtocolMismatch(
                        format!("{:?}", ty),
                        format!("{:?}", bound),
                    ))
                    .with_no_span()
                }
                BoundCheckResult::DoesNotMatchBecause(detail) => {
                    return Err(CodeErrorKind::ProtocolMismatchDetail(
                        format!("{:?}", ty),
                        format!("{:?}", bound),
                        detail,
                    ))
                    .with_no_span()
                }
            }
        }
        Ok(())
    }

    fn check_protocol_bound(
        &mut self,
        bound: ir::TyP<'ir>,
        ty: ir::TyP<'ir>,
    ) -> Result<BoundCheckResult, AluminaError> {
        // TODO: this can be cached, as it's quite expensive to check
        let protocol = match bound {
            ir::Ty::Protocol(protocol) => protocol.get_protocol(),
            _ => {
                // Exact type match is not really that useful, but we allow it.
                if bound == ty {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
        };

        // TODO: Logic for builtin protocols
        let named_type = match ty {
            ir::Ty::NamedType(named_type) => *named_type,
            _ => {
                return Ok(BoundCheckResult::DoesNotMatch);
            }
        };

        let associated_fns = self.get_associated_fns(named_type);
        for fun in protocol.methods {
            let item = match associated_fns.get(fun.name) {
                Some(fun) => fun,
                None => {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                        "missing method `{}`",
                        fun.name
                    )))
                }
            };

            if item.get_function().placeholders.len() > 0 {
                return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                    "`{}` is a generic function",
                    fun.name
                )));
            }

            let monomorphized = self
                .monomorphize_item(MonomorphizeKey(item, &[]))?
                .get_function();

            if monomorphized.args.len() != fun.arg_types.len() {
                return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                    "`{}` has wrong number of parameters",
                    fun.name
                )));
            }

            for (arg, expected) in monomorphized.args.iter().zip(fun.arg_types.iter()) {
                if arg.ty != *expected {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                        "`{}` has parameters of wrong type",
                        fun.name
                    )));
                }
            }

            if monomorphized.return_type != fun.return_type {
                return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                    "`{}` has a wrong return type",
                    fun.name
                )));
            }
        }

        Ok(BoundCheckResult::Matches)
    }

    fn monomorphize_static_or_const(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::StaticOrConst<'ast>,
    ) -> Result<(), AluminaError> {
        let mut child = Self::new(self.mono_ctx);

        let typ = s.typ.map(|t| child.lower_type(t)).transpose()?;
        let mut init = s.init.map(|t| child.lower_expr(t, typ)).transpose()?;

        if s.is_const {
            // No try_qualify_type here, we want strings to remain unqualified in consts
            let init = if let Some(typ) = typ {
                child
                    .try_coerce(typ, init.unwrap())
                    .append_span(s.init.unwrap().span)?
            } else {
                init.unwrap()
            };

            let value = ir::const_eval::const_eval(init)
                .map_err(|_| CodeErrorKind::CannotConstEvaluate)
                .with_span(s.init.unwrap().span)?;

            let res = ir::IRItem::Const(ir::Const {
                name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                value,
            });

            item.assign(res);
        } else {
            let typ = typ.or(init.map(|i| i.ty)).unwrap();
            let typ = child.try_qualify_type(typ)?;
            if let Some(init) = &mut init {
                *init = child.try_coerce(typ, init)?;
            }

            let res = ir::IRItem::Static(ir::Static {
                name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                typ,
                init,
            });
            item.assign(res);

            child
                .mono_ctx
                .static_local_defs
                .insert(item, child.local_defs);
        }

        Ok(())
    }

    fn monomorphize_function(
        &mut self,
        item: ir::IRItemP<'ir>,
        func: &ast::Function<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        if generic_args.len() != func.placeholders.len() {
            return Err(CodeErrorKind::GenericParamCountMismatch(
                func.placeholders.len(),
                generic_args.len(),
            ))
            .with_no_span();
        }

        let replacements = func
            .placeholders
            .iter()
            .zip(generic_args.iter())
            .map(|(&k, &v)| (k.id, v));

        let mut child = if func.closure {
            // Closures can bind the generic parameters of the enclosing function, so we need
            // to copy them over.
            Self::with_replacements(
                self.mono_ctx,
                replacements
                    .chain(self.replacements.iter().map(|(&k, &v)| (k, v)))
                    .collect(),
            )
        } else {
            Self::with_replacements(self.mono_ctx, replacements.collect())
        };

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in func.placeholders.iter().zip(generic_args.iter()) {
            for bound in placeholder.bounds {
                let bound = child.lower_type(bound)?;
                protocol_bounds.push((bound, ty.clone()));
            }
        }
        child.check_protocol_bounds(protocol_bounds)?;

        let parameters = func
            .args
            .iter()
            .map(|p| {
                let param = ir::Parameter {
                    id: child.mono_ctx.map_id(p.id),
                    ty: child.lower_type(p.typ)?,
                };
                child.local_types.insert(param.id, param.ty);
                Ok(param)
            })
            .collect::<Result<Vec<_>, AluminaError>>()?;

        let return_type = child.lower_type(func.return_type)?;
        let res = ir::IRItem::Function(ir::Function {
            name: func.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            attributes: func.attributes.alloc_on(child.mono_ctx.ir),
            args: &parameters.alloc_on(child.mono_ctx.ir),
            return_type,
            body: OnceCell::new(),
        });
        item.assign(res);

        // We need the item to be assigned before we monomorphize the body, as the
        // function can be recursive and we need to be able to get the signature for
        // typechecking purposes.

        child.return_type = Some(return_type);
        if let Some(body) = func.body {
            let body = child.lower_function_body(body)?;
            item.get_function().body.set(body).unwrap();
        }

        Ok(())
    }

    pub fn lower_function_body(
        mut self,
        expr: ast::ExprP<'ast>,
    ) -> Result<ir::FuncBody<'ir>, AluminaError> {
        let return_type = self.return_type.unwrap();
        let body = self
            .lower_expr(expr, Some(return_type))
            .append_span(expr.span)?;

        let body = self.try_coerce(return_type, body).append_span(expr.span)?;

        let mut statements = Vec::new();

        if self.defer_context.is_some() {
            self.generate_defer_prologue(&mut statements);
        }

        if let ir::ExprKind::Block(block, ret) = body.kind {
            statements.extend(block.iter().cloned());
            statements.push(ir::Statement::Expression(self.make_return(ret)?));
        } else {
            statements.push(ir::Statement::Expression(self.make_return(body)?));
        };

        if self.defer_context.is_some() {
            self.generate_defer_epilogue(&mut statements);
        }

        let function_body = FuncBody {
            statements: statements.alloc_on(self.mono_ctx.ir),
            local_defs: self.local_defs.alloc_on(self.mono_ctx.ir),
        };

        let elider = ZstElider::new(self.mono_ctx.ir);
        let optimized = elider.elide_zst_func_body(function_body);

        Ok(optimized)
    }

    pub fn monomorphize_item(
        &mut self,
        key: MonomorphizeKey<'ast, 'ir>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let item: ir::IRItemP = match self.mono_ctx.finished.entry(key.clone()) {
            // The cell may be empty at this point if we are dealing with recursive references
            // In this case, we will just return the item as is, but it will not
            // be populated until the top-level item is finished.
            indexmap::map::Entry::Occupied(entry) => {
                if entry.get().try_get().is_none() {
                    match key.0.get() {
                        ast::Item::StaticOrConst(_) => {
                            return Err(CodeErrorKind::RecursiveStaticInitialization).with_no_span()
                        }
                        _ => {}
                    }
                }
                return Ok(entry.get());
            }
            indexmap::map::Entry::Vacant(entry) => {
                let symbol = self.mono_ctx.ir.make_symbol();
                self.mono_ctx.reverse_map.insert(symbol, key.clone());
                entry.insert(symbol)
            }
        };

        match key.0.get() {
            ast::Item::Enum(en) => {
                self.monomorphize_enum(item, en, key.1)
                    .append_mono_marker()?;
            }
            ast::Item::Function(func) => {
                self.monomorphize_function(item, func, key.1)
                    .append_mono_marker()?;
            }
            ast::Item::StructLike(s) => {
                self.monomorphize_struct(item, s, key.1)
                    .append_span(s.span)
                    .append_mono_marker()?;
            }
            ast::Item::StaticOrConst(s) => {
                self.monomorphize_static_or_const(item, s)
                    .append_mono_marker()?;
            }
            ast::Item::Macro(_) => {
                unreachable!("macros should have been expanded by now");
            }
            ast::Item::BuiltinMacro(_) => {
                unreachable!("macros should have been expanded by now");
            }
            ast::Item::Intrinsic(_) => {
                unreachable!("intrinsics shouldn't be monomorphized");
            }
            ast::Item::Protocol(p) => {
                self.monomorphize_protocol(item, p, key.1)
                    .append_mono_marker()?;
            }
        };

        Ok(item)
    }

    pub fn generate_static_constructor(&mut self) -> Result<(), AluminaError> {
        let item = self.mono_ctx.ir.make_symbol();
        self.return_type = Some(self.types.builtin(BuiltinType::Void));

        let (statements, local_defs): (Vec<_>, Vec<_>) = self
            .mono_ctx
            .finished
            .iter()
            .filter_map(|(_, v)| match v.get() {
                ir::IRItem::Static(s) if s.init.is_some() => Some((v, s)),
                _ => None,
            })
            .map(|(v, s)| {
                (
                    ir::Statement::Expression(
                        self.exprs.assign(self.exprs.static_var(v), s.init.unwrap()),
                    ),
                    self.mono_ctx.static_local_defs.get(v).unwrap().clone(),
                )
            })
            .rev()
            .unzip();

        let local_defs = local_defs.into_iter().flatten().collect::<Vec<_>>();

        let body = self.exprs.block(
            statements,
            self.exprs
                .void(self.types.builtin(BuiltinType::Void), ir::ValueType::RValue),
        );

        let mut statements = Vec::new();
        if let ir::ExprKind::Block(block, ret) = body.kind {
            statements.extend(block.iter().cloned());
            statements.push(ir::Statement::Expression(self.make_return(ret)?));
        } else {
            statements.push(ir::Statement::Expression(self.make_return(body)?));
        };

        let function_body = FuncBody {
            statements: statements.alloc_on(self.mono_ctx.ir),
            local_defs: local_defs.alloc_on(self.mono_ctx.ir),
        };

        let elider = ZstElider::new(self.mono_ctx.ir);
        let optimized = elider.elide_zst_func_body(function_body);

        item.assign(ir::IRItem::Function(ir::Function {
            name: None,
            attributes: [Attribute::StaticConstructor].alloc_on(self.mono_ctx.ir),
            args: &[].alloc_on(self.mono_ctx.ir),
            return_type: self.types.builtin(BuiltinType::Void),
            body: OnceCell::from(optimized),
        }));

        self.mono_ctx.extra_items.push(item);
        Ok(())
    }

    pub fn monomorphize_lang_item<I>(
        &mut self,
        kind: LangItemKind,
        generic_args: I,
    ) -> Result<ir::IRItemP<'ir>, AluminaError>
    where
        I: IntoIterator<Item = ir::TyP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let item = self.mono_ctx.lang_items.get(kind).with_no_span()?;
        let args = self.mono_ctx.ir.arena.alloc_slice_fill_iter(generic_args);
        let key = MonomorphizeKey(item, args);

        self.monomorphize_item(key)
    }

    fn slice_of(
        &mut self,
        inner: ir::TyP<'ir>,
        is_const: bool,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        let ptr_type = self.types.pointer(inner, is_const);
        let item = self.monomorphize_lang_item(LangItemKind::Slice, [ptr_type])?;
        Ok(self.types.named(item))
    }

    fn dyn_ptr_of(&mut self, is_const: bool) -> Result<ir::TyP<'ir>, AluminaError> {
        let ptr_type = self
            .types
            .pointer(self.types.builtin(BuiltinType::Void), is_const);
        let item = self.monomorphize_lang_item(LangItemKind::DynPtr, [ptr_type])?;
        Ok(self.types.named(item))
    }

    pub fn lower_type(&mut self, typ: ast::TyP<'ast>) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *typ {
            ast::Ty::Builtin(kind) => self.types.builtin(kind),
            ast::Ty::Array(inner, len) => {
                let inner = self.lower_type(inner)?;
                self.types.array(inner, len)
            }
            ast::Ty::Pointer(inner, is_const) => {
                let inner = self.lower_type(inner)?;
                self.types.pointer(inner, is_const)
            }
            ast::Ty::Slice(inner, is_const) => {
                let inner = self.lower_type(inner)?;
                self.slice_of(inner, is_const)?
            }
            ast::Ty::Dyn(is_const) => self.dyn_ptr_of(is_const)?,
            ast::Ty::Extern(id) => self.types.r#extern(self.mono_ctx.map_id(id)),
            ast::Ty::Fn(args, ret) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower_type(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = self.lower_type(ret)?;
                self.types.function(args, ret)
            }
            ast::Ty::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|arg| self.lower_type(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                self.types.tuple(items)
            }
            ast::Ty::Placeholder(id) => self
                .replacements
                .get(&id)
                .copied()
                .expect("unbound placeholder"),

            ast::Ty::NamedType(item) => {
                let key = MonomorphizeKey(item, &[]);
                let item = self.monomorphize_item(key)?;
                self.types.named(item)
            }
            ast::Ty::GenericType(item, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir);

                let key = MonomorphizeKey(item, args);
                let ir_item = self.monomorphize_item(key)?;
                if let ast::Item::Protocol(_) = item.get() {
                    self.types.protocol(ir_item)
                } else {
                    self.types.named(ir_item)
                }
            }
            ast::Ty::Protocol(item) => {
                let key = MonomorphizeKey(item, &[]);
                let item = self.monomorphize_item(key)?;
                self.types.protocol(item)
            }
        };

        Ok(result)
    }

    fn get_struct_field_map(
        &mut self,
        item: ir::IRItemP<'ir>,
    ) -> HashMap<&'ast str, &'ir ir::Field<'ir>> {
        let MonomorphizeKey(ast_item, _) = self.mono_ctx.reverse_lookup(item);
        let ir_struct = item.get_struct_like();
        let ast_struct = ast_item.get_struct_like();

        ast_struct
            .fields
            .iter()
            .map(|ast_f| {
                ir_struct
                    .fields
                    .iter()
                    .find(|ir_f| self.mono_ctx.map_id(ast_f.id) == ir_f.id)
                    .map(|f| (ast_f.name, f))
                    .unwrap()
            })
            .collect()
    }

    fn get_associated_fns_ast(
        &self,
        item: ast::ItemP<'ast>,
    ) -> HashMap<&'ast str, ast::ItemP<'ast>> {
        match item.get() {
            ast::Item::StructLike(s) => s.associated_fns.iter().map(|f| (f.name, f.item)).collect(),
            ast::Item::Enum(e) => e.associated_fns.iter().map(|f| (f.name, f.item)).collect(),
            _ => panic!("does not have associated fns"),
        }
    }

    fn get_associated_fns(
        &mut self,
        item: ir::IRItemP<'ir>,
    ) -> HashMap<&'ast str, ast::ItemP<'ast>> {
        let MonomorphizeKey(ast_item, _) = self.mono_ctx.reverse_lookup(item);
        self.get_associated_fns_ast(ast_item)
    }

    fn make_tentative_child<'b>(&'b mut self) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = self.mono_ctx.ir;

        // this should be some CoW thing, cloning everything here is excessive
        Monomorphizer {
            mono_ctx: self.mono_ctx,
            replacements: self.replacements.clone(),
            local_types: self.local_types.clone(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: self.return_type,
            loop_contexts: self.loop_contexts.clone(),
            local_defs: self.local_defs.clone(),
            defer_context: self.defer_context.clone(),
        }
    }

    fn try_qualify_type(&mut self, typ: ir::TyP<'ir>) -> Result<ir::TyP<'ir>, AluminaError> {
        if let ir::Ty::Unqualified(UnqualifiedKind::String(_)) = typ {
            return Ok(self.slice_of(self.types.builtin(BuiltinType::U8), true)?);
        }

        return Ok(typ);
    }

    fn try_coerce(
        &mut self,
        lhs_typ: ir::TyP<'ir>,
        rhs: ir::ExprP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if lhs_typ.assignable_from(rhs.ty) {
            return Ok(rhs);
        }

        let lhs_lang = self.mono_ctx.get_lang_type_kind(lhs_typ);
        let rhs_lang = self.mono_ctx.get_lang_type_kind(rhs.ty);

        // unqualified string -> slice
        match (&lhs_lang, rhs.ty) {
            (
                Some(LangTypeKind::Slice(ir::Ty::Pointer(ir::Ty::Builtin(BuiltinType::U8), true))),
                ir::Ty::Unqualified(UnqualifiedKind::String(size)),
            ) => {
                let ptr_type = self
                    .types
                    .pointer(self.types.builtin(BuiltinType::U8), true);
                let size_lit = self.exprs.lit(
                    ir::Lit::Int(*size as u128),
                    self.types.builtin(BuiltinType::USize),
                );

                let item = self.monomorphize_lang_item(LangItemKind::SliceNew, [ptr_type])?;
                let func = self.exprs.function(item);
                return Ok(self.exprs.call(
                    func,
                    [rhs, size_lit].into_iter(),
                    item.get_function().return_type,
                ));
            }
            _ => {}
        }

        match (&lhs_lang, rhs_lang) {
            // &mut [T] -> &[T]
            (Some(LangTypeKind::Slice(t1_ptr)), Some(LangTypeKind::Slice(t2_ptr))) => {
                match (t1_ptr, t2_ptr) {
                    (ir::Ty::Pointer(t1, true), ir::Ty::Pointer(t2, _)) if t1 == t2 => {
                        let item = self.monomorphize_lang_item(LangItemKind::SliceCoerce, [*t1])?;

                        let func = self.exprs.function(item);
                        return Ok(self.exprs.call(func, [rhs].into_iter(), lhs_typ));
                    }
                    _ => {}
                }
            }
            // &mut dyn -> &dyn
            (Some(LangTypeKind::Dyn(t1_ptr)), Some(LangTypeKind::Dyn(_))) => match t1_ptr {
                ir::Ty::Pointer(_, true) => {
                    let item = self.monomorphize_lang_item(LangItemKind::DynPtrCoerce, [])?;
                    let func = self.exprs.function(item);
                    return Ok(self.exprs.call(func, [rhs].into_iter(), lhs_typ));
                }
                _ => {}
            },
            _ => {}
        }

        // &[T; size] -> &[T]
        // &mut [T; size] -> &[T]
        // &mut [T; size] -> &mut [T]
        // This coercion should be a lang function when we support const usize generics
        match (&lhs_lang, rhs.ty) {
            (
                Some(LangTypeKind::Slice(t1_ptr)),
                ir::Ty::Pointer(ir::Ty::Array(t2, size), t2_const),
            ) => match t1_ptr {
                ir::Ty::Pointer(t1, t1_const)
                    if *t1 == *t2 && (*t1_const || (!*t1_const && !t2_const)) =>
                {
                    let size_lit = self.exprs.lit(
                        ir::Lit::Int(*size as u128),
                        self.types.builtin(BuiltinType::USize),
                    );

                    let item = self.monomorphize_lang_item(LangItemKind::SliceNew, [*t1_ptr])?;

                    let func = self.exprs.function(item);

                    let data = self
                        .exprs
                        .r#ref(self.exprs.const_index(self.exprs.deref(rhs), 0));

                    return Ok(self.exprs.call(
                        func,
                        [data, size_lit],
                        item.get_function().return_type,
                    ));
                }
                _ => {}
            },
            _ => {}
        }

        // &T -> &dyn
        // &mut T -> &dyn
        // &mut T -> &mut dyn
        match (&lhs_lang, rhs.ty) {
            (Some(LangTypeKind::Dyn(t1_ptr)), ir::Ty::Pointer(t2, t2_const)) => match t1_ptr {
                ir::Ty::Pointer(_, t1_const) if (*t1_const || (!*t1_const && !*t2_const)) => {
                    let item = if *t1_const {
                        self.monomorphize_lang_item(LangItemKind::DynPtrNewConst, [*t2])?
                    } else {
                        self.monomorphize_lang_item(LangItemKind::DynPtrNewMut, [*t2])?
                    };

                    let func = self.exprs.function(item);

                    return Ok(self
                        .exprs
                        .call(func, [rhs], item.get_function().return_type));
                }
                _ => {}
            },
            _ => {}
        }

        Err(mismatch!(lhs_typ, rhs.ty)).with_no_span()
    }

    fn try_resolve_function(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&[ast::TyP<'ast>]>,
        self_expr: Option<ir::ExprP<'ir>>,
        tentative_args: Option<&[ast::ExprP<'ast>]>,
        return_type_hint: Option<ir::TyP<'ir>>,
        args_hint: Option<&[ir::TyP<'ir>]>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let fun = item.get_function();

        // If the function is not generic, we don't need to infer the args
        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            return self.monomorphize_item(MonomorphizeKey(item, generic_args));
        }

        if fun.placeholders.is_empty() {
            return self.monomorphize_item(MonomorphizeKey(item, &[]));
        }

        // If the function is generic but no args are provided, we can try to infer the args
        // based on the types of the function's parameters and provided arguments in matching
        // positions and the return type with type_hint Since we have not yet monomorphized the
        // arguments, we do so tentatively in a fresh monomorphizer without the type_hint.
        // If the monomorphization of an argument fails for whatever reason, we skip that arg,
        // but do not rethrow the error as the resolution might still succeed.

        let mut infer_pairs = Vec::new();

        let self_slot = match self_expr {
            Some(self_expr) => Some((fun.args[0].typ, self_expr.ty)),
            None => None,
        };

        let mut tentative_errors = Vec::new();
        if let Some(args) = tentative_args {
            let self_count = self_expr.iter().count();

            if fun.args.len() != args.len() + self_count {
                return Err(CodeErrorKind::ParamCountMismatch(
                    fun.args.len() - self_count,
                    args.len(),
                ))
                .with_no_span();
            }

            let mut child = self.make_tentative_child();
            infer_pairs.extend(
                fun.args
                    .iter()
                    .skip(self_count)
                    .zip(args.iter())
                    .filter_map(|(p, e)| match child.lower_expr(e, None) {
                        Ok(e) => Some(Ok((p.typ, e.ty))),
                        Err(AluminaError::CodeErrors(errors)) => {
                            tentative_errors.extend(
                                errors.into_iter().filter(|f| {
                                    !matches!(f.kind, CodeErrorKind::TypeInferenceFailed)
                                }),
                            );
                            None
                        }
                        Err(e) => Some(Err(e)),
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );

            if !tentative_errors.is_empty() {
                return Err(AluminaError::CodeErrors(tentative_errors));
            }
        }

        if let Some(args_hint) = args_hint {
            assert!(tentative_args.is_none());
            assert!(self_slot.is_none());

            infer_pairs.extend(
                fun.args
                    .iter()
                    .zip(args_hint.iter())
                    .map(|(p, e)| (p.typ, *e)),
            );
        }

        if let Some(return_type_hint) = return_type_hint {
            infer_pairs.push((fun.return_type, return_type_hint));
        }

        let mut type_inferer = TypeInferer::new(
            self.mono_ctx,
            fun.placeholders.iter().map(|p| p.id).collect(),
        );

        match type_inferer.try_infer(self_slot, infer_pairs) {
            Some(generic_args) => self.monomorphize_item(MonomorphizeKey(
                item,
                generic_args.alloc_on(self.mono_ctx.ir),
            )),
            None => Err(CodeErrorKind::TypeInferenceFailed).with_no_span(),
        }
    }

    fn try_resolve_struct(
        &mut self,
        typ: ast::TyP<'ast>,
        initializers: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let (item, generic_args) = match typ {
            ast::Ty::NamedType(item) => (*item, None),
            ast::Ty::GenericType(item, generic_args) => (*item, Some(*generic_args)),
            _ => {
                let lowered = self.lower_type(typ)?;
                match lowered {
                    ir::Ty::NamedType(item) if item.is_struct_like() => return Ok(item),
                    _ => return Err(CodeErrorKind::StructLikeExpectedHere).with_no_span(),
                }
            }
        };

        let r#struct = match item.get() {
            ast::Item::StructLike(s) => s,
            _ => return Err(CodeErrorKind::StructLikeExpectedHere).with_no_span(),
        };

        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            return self.monomorphize_item(MonomorphizeKey(item, generic_args));
        }

        // If the struct is not generic, we don't need to infer the args
        if r#struct.placeholders.is_empty() {
            return self.monomorphize_item(MonomorphizeKey(item, &[]));
        }

        // If the parent of this expression expects a specific struct, we trust that this is
        // in fact the correct monomorphization.
        if let Some(ir::Ty::NamedType(hint_item)) = type_hint {
            let MonomorphizeKey(ast_hint_item, _) = self.mono_ctx.reverse_lookup(hint_item);
            if item == ast_hint_item {
                return Ok(hint_item);
            }
        }

        // See notes in try_resolve_function. Same thing, but for struct fields (we match by name instead of position).

        let mut tentative_errors = Vec::new();
        let mut child = self.make_tentative_child();
        let pairs: Vec<_> = r#struct
            .fields
            .iter()
            .filter_map(|f| {
                initializers
                    .iter()
                    .find(|i| i.name == f.name)
                    .map(|i| (f, i))
            })
            .filter_map(|(p, e)| match child.lower_expr(e.value, None) {
                Ok(e) => Some(Ok((p.typ, e.ty))),
                Err(AluminaError::CodeErrors(errors)) => {
                    tentative_errors.extend(
                        errors
                            .into_iter()
                            .filter(|f| !matches!(f.kind, CodeErrorKind::TypeInferenceFailed)),
                    );
                    None
                }
                Err(e) => Some(Err(e)),
            })
            .collect::<Result<_, _>>()?;

        if !tentative_errors.is_empty() {
            return Err(AluminaError::CodeErrors(tentative_errors));
        }

        let mut type_inferer = TypeInferer::new(
            self.mono_ctx,
            r#struct.placeholders.iter().map(|p| p.id).collect(),
        );
        let infer_result = type_inferer.try_infer(None, pairs);

        match infer_result {
            Some(generic_args) => self.monomorphize_item(MonomorphizeKey(
                item,
                generic_args.alloc_on(self.mono_ctx.ir),
            )),
            None => Err(CodeErrorKind::TypeInferenceFailed).with_no_span(),
        }
    }

    fn r#ref(&mut self, expr: ir::ExprP<'ir>) -> ir::ExprP<'ir> {
        if matches!(expr.value_type, ValueType::LValue) {
            return self.exprs.r#ref(expr);
        }

        let id = self.mono_ctx.ir.make_id();
        self.local_defs.push(ir::LocalDef { id, typ: expr.ty });
        self.local_types.insert(id, expr.ty);

        let local = self.exprs.local(id, expr.ty);
        self.exprs.block(
            [ir::Statement::Expression(self.exprs.assign(local, expr))],
            self.exprs.r#ref(local),
        )
    }

    fn autoref(
        &mut self,
        expr: ir::ExprP<'ir>,
        target: ir::TyP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let mut a: isize = 0;
        let mut a_typ = expr.ty;
        while let ir::Ty::Pointer(inner, _) = a_typ {
            a += 1;
            a_typ = inner;
        }

        let mut b: isize = 0;
        let mut b_typ = target;
        while let ir::Ty::Pointer(inner, _) = b_typ {
            b += 1;
            b_typ = *inner;
        }

        match a - b {
            0 => Ok(expr),
            n if n < 0 => {
                let mut expr = expr;
                for _ in 0..-n {
                    expr = self.r#ref(expr);
                }
                Ok(expr)
            }
            n if n > 0 => {
                let mut expr = expr;
                for _ in 0..n {
                    expr = self.exprs.deref(expr);
                }
                Ok(expr)
            }
            _ => unreachable!(),
        }
    }

    fn typecheck_binary(
        &mut self,
        op: ast::BinOp,
        lhs: ir::ExprP<'ir>,
        rhs: ir::ExprP<'ir>,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let result_typ = match (lhs.ty, op, rhs.ty) {
            // Integer builtin types
            (
                Builtin(l),
                BitAnd | BitAnd | BitOr | BitXor | Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus
                | Mul | Div | Mod,
                Builtin(r),
            ) if l == r && l.is_integer() => {
                if op.is_comparison() {
                    self.types.builtin(BuiltinType::Bool)
                } else {
                    lhs.ty
                }
            }

            (NamedType(l), Eq | Neq, NamedType(r))
                if l == r && matches!(l.get(), ir::IRItem::Enum(_)) =>
            {
                self.types.builtin(BuiltinType::Bool)
            }

            (Builtin(l), LShift | RShift, Builtin(r)) if l.is_integer() && r.is_integer() => lhs.ty,

            // Float builting types
            (Builtin(l), Eq | Neq | Lt | LEq | Gt | GEq | Plus | Minus | Mul | Div, Builtin(r))
                if l == r && l.is_float() =>
            {
                if op.is_comparison() {
                    self.types.builtin(BuiltinType::Bool)
                } else {
                    lhs.ty
                }
            }

            // Logical operators
            (
                Builtin(BuiltinType::Bool),
                And | Or | BitXor | Eq | Neq,
                Builtin(BuiltinType::Bool),
            ) => self.types.builtin(BuiltinType::Bool),

            // Pointer comparison and pointer difference
            (Pointer(l, _), Eq | Neq | Lt | LEq | Gt | GEq, Pointer(r, _)) if l == r => {
                self.types.builtin(BuiltinType::Bool)
            }

            (Pointer(l, l_const), Minus, Pointer(r, r_const)) if l == r && l_const == r_const => {
                self.types.builtin(BuiltinType::ISize)
            }

            // Pointer arithmetic
            (Pointer(_l, _), Plus | Minus, Builtin(BuiltinType::ISize | BuiltinType::USize)) => {
                lhs.ty
            }

            _ => {
                return Err(CodeErrorKind::InvalidBinOp(
                    op,
                    format!("{:?}", lhs.ty),
                    format!("{:?}", rhs.ty),
                ))
                .with_no_span()
            }
        };

        Ok(result_typ)
    }

    fn lower_stmt(
        &mut self,
        stmt: &ast::Statement<'ast>,
    ) -> Result<Option<ir::Statement<'ir>>, AluminaError> {
        let result = match &stmt.kind {
            ast::StatementKind::Expression(expr) => {
                let expr = self.lower_expr(expr, None)?;
                Some(ir::Statement::Expression(expr))
            }
            ast::StatementKind::LetDeclaration(decl) => {
                let id = self.mono_ctx.map_id(decl.id);
                let type_hint = decl.typ.map(|t| self.lower_type(t)).transpose()?;
                let init = decl
                    .value
                    .map(|v| self.lower_expr(v, type_hint))
                    .transpose()?;

                match (type_hint, init) {
                    (None, None) => {
                        return Err(CodeErrorKind::TypeHintRequired).with_span(stmt.span)
                    }
                    (Some(ty), None) => {
                        self.local_types.insert(id, ty);
                        self.local_defs.push(ir::LocalDef { id, typ: ty });
                        None
                    }
                    (None, Some(init)) => {
                        let typ = self.try_qualify_type(init.ty)?;

                        self.local_types.insert(id, typ);
                        self.local_defs.push(ir::LocalDef { id, typ: typ });

                        if init.diverges() {
                            return Ok(Some(ir::Statement::Expression(init)));
                        }

                        let init = self.try_coerce(typ, init)?;
                        Some(ir::Statement::Expression(
                            self.exprs.assign(self.exprs.local(id, init.ty), init),
                        ))
                    }
                    (Some(ty), Some(init)) => {
                        self.local_types.insert(id, ty);
                        self.local_defs.push(ir::LocalDef { id, typ: ty });

                        if init.diverges() {
                            return Ok(Some(ir::Statement::Expression(init)));
                        }

                        let init = self.try_coerce(ty, init)?;
                        Some(ir::Statement::Expression(
                            self.exprs.assign(self.exprs.local(id, ty), init),
                        ))
                    }
                }
            }
        };

        Ok(result)
    }

    fn lower_block(
        &mut self,
        statements: &'ast [ast::Statement<'ast>],
        ret: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let (statements, errors): (Vec<_>, Vec<_>) = statements
            .iter()
            .map(|stmt| self.lower_stmt(stmt))
            .partition(|f| f.is_ok());

        if !errors.is_empty() {
            let mut combined = Vec::new();
            for error in errors {
                match error.unwrap_err() {
                    AluminaError::CodeErrors(vec) => combined.extend(vec),
                    e => return Err(e),
                }
            }
            return Err(AluminaError::CodeErrors(combined));
        }

        let ret = self.lower_expr(ret, type_hint)?;

        Ok(self
            .exprs
            .block(statements.into_iter().flat_map(|e| e.unwrap()), ret))
    }

    fn lower_lit(
        &mut self,
        ret: &ast::Lit<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let result = match ret {
            ast::Lit::Bool(v) => self.exprs.lit(
                ir::Lit::Bool(*v),
                self.types.builtin(ast::BuiltinType::Bool),
            ),
            ast::Lit::Null => {
                let ty = match type_hint {
                    Some(ir::Ty::Pointer(inner, is_const)) => self.types.pointer(inner, *is_const),
                    _ => self
                        .types
                        .pointer(self.types.builtin(BuiltinType::Void), true),
                };

                self.exprs.lit(ir::Lit::Null, ty)
            }
            ast::Lit::Int(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => self.types.builtin(*t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_integer() => self.types.builtin(*k),
                    _ => self.types.builtin(BuiltinType::I32),
                };

                self.exprs.lit(ir::Lit::Int(*v), ty)
            }
            ast::Lit::Float(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => self.types.builtin(*t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_float() => self.types.builtin(*k),
                    _ => self.types.builtin(BuiltinType::F64),
                };

                self.exprs
                    .lit(ir::Lit::Float(v.alloc_on(self.mono_ctx.ir)), ty)
            }
            ast::Lit::Str(v) => {
                let ptr_type = self
                    .mono_ctx
                    .ir
                    .intern_type(ir::Ty::Unqualified(UnqualifiedKind::String(v.len())));

                self.exprs.lit(
                    ir::Lit::Str(self.mono_ctx.ir.arena.alloc_slice_copy(v)),
                    ptr_type,
                )
            }
        };

        Ok(result)
    }

    fn lower_deref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(inner, type_hint.map(|ty| self.types.pointer(ty, true)))?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.ty {
            ir::Ty::Pointer(_, _) => self.exprs.deref(inner),
            _ => return Err(mismatch!("pointer", inner.ty)).with_no_span(),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_ref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let type_hint = match type_hint {
            Some(ir::Ty::Pointer(inner, _)) => Some(*inner),
            Some(hint) => {
                if let Some(LangTypeKind::Slice(ir::Ty::Pointer(ty, _))) =
                    self.mono_ctx.get_lang_type_kind(hint)
                {
                    Some(self.types.array(ty, 0))
                } else {
                    None
                }
            }
            None => None,
        };

        let inner = self.lower_expr(inner, type_hint)?;
        if inner.diverges() {
            return Ok(inner);
        }

        let typ = self.try_qualify_type(inner.ty)?;
        let inner = self.try_coerce(typ, inner)?;

        Ok(self.r#ref(inner))
    }

    fn lower_local(
        &mut self,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let id = self.mono_ctx.map_id(id);
        let typ = self
            .local_types
            .get(&id)
            .copied()
            .ok_or({
                //unsafe {std::intrinsics::breakpoint(); }
                CodeErrorKind::LocalWithUnknownType
            })
            .with_no_span()?;

        Ok(self.exprs.local(id, typ))
    }

    fn lower_static(
        &mut self,
        item: ast::ItemP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.monomorphize_item(MonomorphizeKey(item, &[]))?;

        Ok(self.exprs.static_var(item_cell))
    }

    fn lower_const(
        &mut self,
        item: ast::ItemP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.monomorphize_item(MonomorphizeKey(item, &[]))?;
        let value = match item_cell.get() {
            ir::IRItem::Const(c) => c.value,
            _ => unreachable!(),
        };

        Ok(self.exprs.const_value(value))
    }

    fn lower_unary(
        &mut self,
        op: ast::UnOp,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(inner, type_hint)?;
        if inner.diverges() {
            return Ok(inner);
        }

        match (op, inner.ty) {
            (ast::UnOp::Not, ir::Ty::Builtin(BuiltinType::Bool)) => {}
            (ast::UnOp::BitNot, ir::Ty::Builtin(b)) if b.is_integer() => {}
            (ast::UnOp::Neg, ir::Ty::Builtin(b))
                if (b.is_integer() && b.is_signed()) || b.is_float() => {}
            _ => {
                return Err(CodeErrorKind::InvalidUnOp(op, format!("{:?}", inner.ty)))
                    .with_no_span()
            }
        };

        Ok(self.exprs.unary(op, inner, inner.ty))
    }

    fn lower_binary(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::ExprP<'ast>,
        rhs: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let lhs = self.lower_expr(
            lhs,
            match op {
                Eq | Neq | GEq | LEq | Lt | Gt => None,
                And | Or => Some(self.types.builtin(BuiltinType::Bool)),
                _ => type_hint,
            },
        )?;

        let rhs = self.lower_expr(
            rhs,
            match op {
                Plus | Minus => match lhs.ty {
                    Pointer(_, _) => Some(self.types.builtin(BuiltinType::ISize)),
                    _ => Some(lhs.ty),
                },
                LShift | RShift => Some(self.types.builtin(BuiltinType::USize)),
                _ => Some(lhs.ty),
            },
        )?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.exprs.diverges([lhs, rhs]));
        }

        let maybe_result_typ = self.typecheck_binary(op, lhs, rhs);

        // Special case for slice equality comparison
        match maybe_result_typ {
            Ok(result_typ) => Ok(self.exprs.binary(op, lhs, rhs, result_typ)),
            Err(e) if op == Eq || op == Neq => {
                let lhs_lang = self.mono_ctx.get_lang_type_kind(lhs.ty);
                let rhs_lang = self.mono_ctx.get_lang_type_kind(rhs.ty);

                match (lhs_lang, rhs_lang) {
                    (_, Some(LangTypeKind::Slice(ir::Ty::Pointer(ty, _))))
                    | (Some(LangTypeKind::Slice(ir::Ty::Pointer(ty, _))), _) => {
                        let const_slice_ty = self.slice_of(ty, true)?;
                        let lhs = self.try_coerce(const_slice_ty, lhs)?;
                        let rhs = self.try_coerce(const_slice_ty, rhs)?;

                        let item = self.monomorphize_lang_item(LangItemKind::SliceEqual, [*ty])?;
                        let func = self.exprs.function(item);

                        let mut expr = self.exprs.call(
                            func,
                            [lhs, rhs].into_iter(),
                            item.get_function().return_type,
                        );

                        if op == Neq {
                            expr = self.exprs.unary(
                                ast::UnOp::Not,
                                expr,
                                self.types.builtin(BuiltinType::Bool),
                            );
                        }

                        Ok(expr)
                    }
                    _ => return Err(e),
                }
            }
            Err(e) => return Err(e),
        }
    }

    fn lower_assign_op(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::ExprP<'ast>,
        rhs: &ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let lhs = self.lower_expr(lhs, None)?;
        let rhs = self.lower_expr(
            rhs,
            match op {
                Plus | Minus => match lhs.ty {
                    Pointer(_, _) => Some(self.types.builtin(BuiltinType::ISize)),
                    _ => Some(lhs.ty),
                },
                LShift | RShift => Some(self.types.builtin(BuiltinType::USize)),
                _ => Some(lhs.ty),
            },
        )?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.exprs.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(CodeErrorKind::CannotAssignToRValue).with_no_span();
        }

        if lhs.is_const {
            return Err(CodeErrorKind::CannotAssignToConst).with_no_span();
        }

        let rhs = self.try_coerce(lhs.ty, rhs)?;

        self.typecheck_binary(op, lhs, rhs)?;

        Ok(self.exprs.assign_op(op, lhs, rhs))
    }

    fn lower_assign(
        &mut self,
        inner: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let lhs = self.lower_expr(inner, None)?;
        let rhs = self.lower_expr(rhs, Some(lhs.ty))?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.exprs.diverges([lhs, rhs]));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(CodeErrorKind::CannotAssignToRValue).with_no_span();
        }

        if lhs.is_const {
            return Err(CodeErrorKind::CannotAssignToConst).with_no_span();
        }

        let rhs = self.try_coerce(lhs.ty, rhs)?;

        Ok(self.exprs.assign(lhs, rhs))
    }

    fn lower_if(
        &mut self,
        cond_: ast::ExprP<'ast>,
        then: ast::ExprP<'ast>,
        els_: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let cond = self.lower_expr(cond_, Some(self.types.builtin(BuiltinType::Bool)))?;
        let then = self.lower_expr(then, type_hint)?;
        let els = self.lower_expr(els_, Some(then.ty))?;

        if cond.diverges() {
            return Ok(cond);
        }

        let cond = self
            .try_coerce(self.types.builtin(BuiltinType::Bool), cond)
            .append_span(cond_.span)?;

        let then_typ = self.try_qualify_type(then.ty)?;
        let els_typ = self.try_qualify_type(els.ty)?;

        let then = self.try_coerce(then_typ, then)?;
        let els = self.try_coerce(els_typ, els)?;

        let gcd = ir::Ty::gcd(then.ty, els.ty);
        if !gcd.assignable_from(then.ty) || !gcd.assignable_from(els.ty) {
            return Err(CodeErrorKind::MismatchedBranchTypes(
                format!("{:?}", then.ty),
                format!("{:?}", els.ty),
            ))
            .with_span(els_.span);
        }

        Ok(self.exprs.if_then(cond, then, els))
    }

    fn lower_tuple(
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
            .map(|(expr, hint)| self.lower_expr(expr, hint))
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(lowered));
        }

        let element_types: Vec<_> = lowered.iter().map(|e| e.ty).collect();
        let tuple_type = self.types.tuple(element_types);

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.exprs.local(temporary, tuple_type);
        self.local_defs.push(ir::LocalDef {
            id: temporary,
            typ: tuple_type,
        });

        let statements = lowered
            .into_iter()
            .enumerate()
            .map(|(i, e)| {
                ir::Statement::Expression(
                    self.exprs.assign(self.exprs.tuple_index(local, i, e.ty), e),
                )
            })
            .collect::<Vec<_>>();

        Ok(self.exprs.block(statements, local))
    }

    fn lower_cast(
        &mut self,
        expr: ast::ExprP<'ast>,
        target_type: ast::TyP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let expr = self.lower_expr(expr, None)?;
        if expr.diverges() {
            return Ok(expr);
        }

        let typ = self.lower_type(target_type)?;

        // If the type coerces automatically, no cast is required
        if let Some(expr) = self.try_coerce(typ, expr).ok() {
            return Ok(expr);
        }

        match (expr.ty, typ) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}

            // Enums
            (ir::Ty::NamedType(a), ir::Ty::Builtin(b))
                if matches!(a.get(), ir::IRItem::Enum(_)) && b.is_numeric() => {}

            // Pointer casts
            (ir::Ty::Pointer(_, _), ir::Ty::Pointer(_, _)) => {
                // Yes, even const -> mut casts, if you do this you are on your own
            }
            (ir::Ty::Builtin(BuiltinType::USize), ir::Ty::Pointer(_, _)) => {}
            (ir::Ty::Pointer(_, _), ir::Ty::Builtin(BuiltinType::USize)) => {}

            _ => {
                return Err(CodeErrorKind::InvalidCast(
                    format!("{:?}", expr.ty),
                    format!("{:?}", typ),
                ))
                .with_no_span()
            }
        }

        Ok(self.exprs.cast(expr, typ))
    }

    fn lower_loop(
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

        let body = self.lower_expr(body, None);
        self.loop_contexts.pop();

        let body = body?;

        let statements = vec![
            ir::Statement::Label(continue_label),
            ir::Statement::Expression(body),
            ir::Statement::Expression(self.exprs.goto(continue_label)),
            ir::Statement::Label(break_label),
        ];

        let result = match self.local_types.get(&loop_result) {
            None => self.exprs.block(statements, self.exprs.unreachable()),
            Some(typ) => {
                self.local_defs.push(ir::LocalDef {
                    id: loop_result,
                    typ: *typ,
                });
                self.exprs
                    .block(statements, self.exprs.local(loop_result, *typ))
            }
        };

        Ok(result)
    }

    fn lower_break(
        &mut self,
        expr: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self
            .loop_contexts
            .last()
            .expect("break outside of loop")
            .clone();

        let expr = expr
            .map(|e| self.lower_expr(e, loop_context.type_hint))
            .transpose()?;

        if expr.map(|e| e.diverges()).unwrap_or(false) {
            return Ok(expr.unwrap());
        }

        let break_typ = expr
            .map(|e| self.try_qualify_type(e.ty))
            .unwrap_or(Ok(self.types.builtin(BuiltinType::Void)))?;

        let slot_type = match self.local_types.entry(loop_context.loop_result) {
            Entry::Vacant(v) => {
                v.insert(break_typ);
                break_typ
            }
            Entry::Occupied(o) => o.get(),
        };

        let expr = expr
            .map(|expr| self.try_coerce(slot_type, expr))
            .transpose()?
            .unwrap_or(
                self.exprs
                    .void(self.types.builtin(BuiltinType::Void), ir::ValueType::RValue),
            );

        let statements = [ir::Statement::Expression(
            self.exprs
                .assign(self.exprs.local(loop_context.loop_result, slot_type), expr),
        )];

        Ok(self
            .exprs
            .block(statements, self.exprs.goto(loop_context.break_label)))
    }

    fn lower_continue(
        &mut self,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self.loop_contexts.last().expect("continue outside of loop");

        Ok(self.exprs.goto(loop_context.continue_label))
    }

    fn lower_intrinsic(
        &mut self,
        callee: &ast::Intrinsic,
        generic_args: &[ast::TyP<'ast>],
        args: &[ast::ExprP<'ast>],
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if callee.generic_count != generic_args.len() {
            return Err(CodeErrorKind::GenericParamCountMismatch(
                callee.generic_count,
                generic_args.len(),
            ))
            .with_no_span();
        }

        if callee.arg_count != args.len() {
            return Err(CodeErrorKind::ParamCountMismatch(
                callee.arg_count,
                args.len(),
            ))
            .with_no_span();
        }

        let generic_args = generic_args
            .iter()
            .map(|e| self.lower_type(e))
            .collect::<Result<Vec<_>, _>>()?;

        let args = args
            .iter()
            .map(|e| self.lower_expr(e, None))
            .collect::<Result<Vec<_>, _>>()?;

        self.mono_ctx
            .intrinsics
            .invoke(callee.kind, &generic_args[..], &args[..])
    }

    fn lower_method_call(
        &mut self,
        self_arg: ast::ExprP<'ast>,
        unified_fn: Option<ast::ItemP<'ast>>,
        name: &'ast str,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<Option<ir::ExprP<'ir>>, AluminaError> {
        let ir_self_arg = self.lower_expr(self_arg, None)?;

        let method = match ir_self_arg.ty.canonical_type() {
            ir::Ty::NamedType(item) => {
                if let ir::IRItem::StructLike(_) = item.get() {
                    let fields = self.get_struct_field_map(item);
                    if fields.contains_key(name) {
                        // This is not a method, but a field (e.g. a function pointer), go back to lower_call
                        // and process it as usual.
                        return Ok(None);
                    }
                }

                self.get_associated_fns(item).get(name).copied()
            }
            _ => None,
        };

        let method = method
            .or(unified_fn)
            .ok_or_else(|| CodeErrorKind::MethodNotFound(name.into()))
            .with_no_span()?;

        let method = self.try_resolve_function(
            method,
            None,
            Some(ir_self_arg),
            Some(args),
            type_hint,
            None,
        )?;

        let callee = self.exprs.function(method);

        let (arg_types, return_type) = match callee.ty {
            ir::Ty::Fn(arg_types, return_type) => (arg_types, return_type),
            _ => unreachable!(),
        };

        if arg_types.is_empty() {
            return Err(CodeErrorKind::NotAMethod).with_no_span();
        }

        if arg_types.len() != args.len() + 1 {
            return Err(CodeErrorKind::ParamCountMismatch(
                arg_types.len() - 1,
                args.len(),
            ))
            .with_no_span();
        }

        let ir_self_arg = self
            .autoref(ir_self_arg, arg_types[0])
            .append_span(self_arg.span)?;
        let mut args = once(Ok(ir_self_arg))
            .chain(
                args.iter()
                    .zip(arg_types.iter().skip(1))
                    .map(|(arg, ty)| self.lower_expr(arg, Some(ty))),
            )
            .collect::<Result<Vec<_>, _>>()?;

        if args.iter().any(|e| e.diverges()) {
            return Ok(Some(self.exprs.diverges(args)));
        }

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, *arg)?;
        }

        Ok(Some(self.exprs.call(callee, args, return_type)))
    }

    fn resolve_defered_func(
        &mut self,
        spec: &ast::DeferredFn<'ast>,
    ) -> Result<ast::ItemP<'ast>, AluminaError> {
        let associated_fns = match spec.typ {
            ast::Ty::Placeholder(id) => {
                let typ = self
                    .replacements
                    .get(id)
                    .ok_or(CodeErrorKind::AssocFnNonNamedType)
                    .with_no_span()?;

                match typ {
                    ir::Ty::NamedType(typ) => self.get_associated_fns(typ),
                    _ => return Err(CodeErrorKind::AssocFnNonNamedType).with_no_span(),
                }
            }
            ast::Ty::NamedType(item) => self.get_associated_fns_ast(item),
            ast::Ty::GenericType(item, _) => self.get_associated_fns_ast(item),
            _ => return Err(CodeErrorKind::AssocFnNonNamedType).with_no_span(),
        };

        let func = associated_fns
            .get(spec.name)
            .ok_or(CodeErrorKind::UnresolvedItem(spec.name.to_string()))
            .with_no_span()?;

        Ok(func)
    }

    fn lower_call(
        &mut self,
        callee: ast::ExprP<'ast>,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // Unlike other AST nodes, calls are handled a bit specially, where we switch on the type of the
        // callee node before lowering it. This is because free-standing function-like values are treated
        // as function pointers, but we are also able to call things that cannot be turned into a function
        // pointer, such as methods, UFCS free functions and compiler intrinsics.
        let callee = match &callee.kind {
            ast::ExprKind::Fn(ast::FnKind::Normal(item), generic_args) => {
                if let ast::Item::Intrinsic(intrinsic) = item.get() {
                    return self.lower_intrinsic(intrinsic, generic_args.unwrap_or(&[]), args);
                }

                let item = self.try_resolve_function(
                    item,
                    *generic_args,
                    None,
                    Some(args),
                    type_hint,
                    None,
                )?;

                self.exprs.function(item)
            }
            ast::ExprKind::Fn(ast::FnKind::Defered(spec), generic_args) => {
                let func = self.resolve_defered_func(spec)?;
                let item = self.try_resolve_function(
                    func,
                    *generic_args,
                    None,
                    Some(args),
                    type_hint,
                    None,
                )?;

                self.exprs.function(item)
            }
            ast::ExprKind::Field(e, field, unified_fn) => {
                // Methods are resolved in the following order - field has precedence, then associated
                // functions, then free functions with UFCS. We never want UFCS to shadow native fields
                // and methods.
                match self.lower_method_call(e, *unified_fn, field, args, type_hint)? {
                    Some(result) => return Ok(result),
                    None => self.lower_expr(callee, None)?,
                }
            }
            _ => self.lower_expr(callee, None)?,
        };

        let (arg_types, return_type) = match callee.ty {
            ir::Ty::Fn(arg_types, return_type) => (arg_types, return_type),
            _ => return Err(CodeErrorKind::FunctionExpectedHere).with_no_span(),
        };

        if arg_types.len() != args.len() {
            return Err(CodeErrorKind::ParamCountMismatch(
                arg_types.len(),
                args.len(),
            ))
            .with_no_span();
        }

        let mut args = args
            .iter()
            .zip(arg_types.iter())
            .map(|(arg, ty)| self.lower_expr(arg, Some(ty)))
            .collect::<Result<Vec<_>, _>>()?;

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, *arg)?;
        }

        if callee.diverges() || args.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(once(callee).chain(args)));
        }

        Ok(self.exprs.call(callee, args, return_type))
    }

    fn lower_fn(
        &mut self,
        kind: ast::FnKind<'ast>,
        generic_args: Option<&'ast [ast::TyP<'ast>]>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // TODO: Forward the type hint inside the function body.

        let (args_hint, return_type_hint) = match type_hint {
            Some(ir::Ty::Fn(args, ret)) => (Some(*args), Some(*ret)),
            _ => (None, None),
        };

        let result = match kind {
            ast::FnKind::Normal(item) => {
                if let ast::Item::Intrinsic(_) = item.get() {
                    return Err(CodeErrorKind::IntrinsicsAreSpecialMkay).with_no_span();
                }

                let item = self.try_resolve_function(
                    item,
                    generic_args,
                    None,
                    None,
                    return_type_hint,
                    args_hint,
                )?;

                self.exprs.function(item)
            }
            ast::FnKind::Defered(spec) => {
                let func = self.resolve_defered_func(&spec)?;

                let item = self.try_resolve_function(
                    func,
                    generic_args,
                    None,
                    None,
                    return_type_hint,
                    args_hint,
                )?;

                self.exprs.function(item)
            }
        };

        Ok(result)
    }

    fn lower_tuple_index(
        &mut self,
        tup: ast::ExprP<'ast>,
        index: usize,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let span = tup.span;
        let tup = self.lower_expr(tup, None)?;
        let result = match tup.ty {
            ir::Ty::Tuple(types) => {
                if types.len() <= index {
                    return Err(CodeErrorKind::TupleIndexOutOfBounds).with_no_span();
                }
                self.exprs.tuple_index(tup, index, types[index])
            }
            _ => return Err(mismatch!("tuple", tup.ty)).with_span(span),
        };

        // We want to typecheck even if it diverges, no point in trying to access
        // tuple fields of non-tuples.
        if tup.diverges() {
            return Ok(tup);
        }

        Ok(result)
    }

    fn lower_field(
        &mut self,
        obj: ast::ExprP<'ast>,
        field: &'ast str,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let obj_span = obj.span;
        let obj = self.lower_expr(obj, None)?;
        let obj_type = self.try_qualify_type(obj.ty)?;
        let obj = self.try_coerce(obj_type, obj)?;

        let result = match obj.ty.canonical_type() {
            ir::Ty::NamedType(item) => {
                let field_map = self.get_struct_field_map(item);
                let field = field_map
                    .get(field)
                    .ok_or(CodeErrorKind::UnresolvedItem(field.to_string()))
                    .with_no_span()?;

                let mut obj = obj;
                while let ir::Ty::Pointer(_, _) = obj.ty {
                    obj = self.exprs.deref(obj);
                }

                self.exprs.field(obj, field.id, field.ty)
            }
            _ => return Err(CodeErrorKind::StructLikeExpectedHere).with_span(obj_span),
        };

        Ok(result)
    }

    fn lower_index(
        &mut self,
        inner: ast::ExprP<'ast>,
        index: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner_span = inner.span;
        let inner = self.lower_expr(inner, type_hint.map(|ty| self.types.pointer(ty, true)))?;
        let inner_type = self.try_qualify_type(inner.ty)?;
        let inner = self.try_coerce(inner_type, inner)?;

        let index = self.lower_expr(index, Some(self.types.builtin(BuiltinType::USize)))?;

        if inner.diverges() || index.diverges() {
            return Ok(self.exprs.diverges([inner, index]));
        }

        let index = self.try_coerce(self.types.builtin(BuiltinType::USize), index)?;

        let result = match inner.ty {
            ir::Ty::Array(_, _) | ir::Ty::Pointer(_, _) => self.exprs.index(inner, index),
            _ => {
                let inner_lang = self.mono_ctx.get_lang_type_kind(inner.ty);

                match inner_lang {
                    Some(LangTypeKind::Slice(ptr_ty)) => {
                        let item =
                            self.monomorphize_lang_item(LangItemKind::SliceIndex, [ptr_ty])?;
                        let func = self.exprs.function(item);
                        return Ok(self.exprs.deref(self.exprs.call(
                            func,
                            [inner, index].into_iter(),
                            ptr_ty,
                        )));
                    }
                    _ => {}
                }

                return Err(mismatch!("array or pointer", inner.ty)).with_span(inner_span);
            }
        };

        Ok(result)
    }

    fn lower_range_index(
        &mut self,
        inner: ast::ExprP<'ast>,
        lower: Option<ast::ExprP<'ast>>,
        upper: Option<ast::ExprP<'ast>>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(
            inner,
            // slice slices to another slice. It could also be an array, but wcyd
            type_hint,
        )?;
        let inner_type = self.try_qualify_type(inner.ty)?;
        let inner = self.try_coerce(inner_type, inner)?;

        let lower = lower
            .map(|e| self.lower_expr(e, Some(self.types.builtin(BuiltinType::USize))))
            .transpose()?;

        let upper = upper
            .map(|e| self.lower_expr(e, Some(self.types.builtin(BuiltinType::USize))))
            .transpose()?;

        let stack = [Some(inner), lower, upper]
            .into_iter()
            .filter_map(|e| e)
            .collect::<Vec<_>>();

        if stack.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(stack));
        }

        let inner_lang = self.mono_ctx.get_lang_type_kind(inner.ty);
        let result = match inner_lang {
            Some(LangTypeKind::Slice(ptr_ty)) => {
                let lower = lower.unwrap_or_else(|| {
                    self.exprs
                        .lit(Lit::Int(0u128), self.types.builtin(BuiltinType::USize))
                });
                match upper {
                    Some(upper) => {
                        let item =
                            self.monomorphize_lang_item(LangItemKind::SliceRangeIndex, [ptr_ty])?;
                        let func = self.exprs.function(item);
                        self.exprs
                            .call(func, [inner, lower, upper].into_iter(), inner.ty)
                    }
                    None => {
                        let item = self
                            .monomorphize_lang_item(LangItemKind::SliceRangeIndexLower, [ptr_ty])?;
                        let func = self.exprs.function(item);
                        self.exprs.call(func, [inner, lower].into_iter(), inner.ty)
                    }
                }
            }
            _ => return Err(CodeErrorKind::RangeIndexNonSlice).with_no_span(),
        };

        Ok(result)
    }

    fn generate_defer_prologue(&self, statements: &mut Vec<ir::Statement<'ir>>) {
        let defer_context = self.defer_context.as_ref().unwrap();

        for (defer_flag, _) in defer_context.defered.iter() {
            statements.push(ir::Statement::Expression(
                self.exprs.assign(
                    self.exprs
                        .local(*defer_flag, self.types.builtin(BuiltinType::Bool)),
                    self.exprs
                        .lit(Lit::Bool(false), self.types.builtin(BuiltinType::Bool)),
                ),
            ));
        }
    }

    fn generate_defer_epilogue(&self, statements: &mut Vec<ir::Statement<'ir>>) {
        let defer_context = self.defer_context.as_ref().unwrap();
        let void = self
            .exprs
            .void(self.types.builtin(BuiltinType::Void), ValueType::RValue);

        statements.push(ir::Statement::Label(defer_context.return_label));
        for (id, expr) in defer_context.defered.iter().rev() {
            statements.push(ir::Statement::Expression(
                ir::Expr::rvalue(
                    ir::ExprKind::If(
                        self.exprs.local(*id, self.types.builtin(BuiltinType::Bool)),
                        expr,
                        void,
                    ),
                    self.types.builtin(BuiltinType::Void),
                )
                .alloc_on(self.mono_ctx.ir),
            ));
        }
        statements.push(ir::Statement::Expression(
            self.exprs.ret(
                self.exprs
                    .local(defer_context.return_local, self.return_type.unwrap()),
            ),
        ));
    }

    fn make_return(&mut self, inner: ir::ExprP<'ir>) -> Result<ir::ExprP<'ir>, AluminaError> {
        if inner.diverges() {
            return Ok(inner);
        }
        let inner = self.try_coerce(self.return_type.unwrap(), inner)?;

        match self.defer_context.as_ref() {
            None | Some(DeferContext { in_defer: true, .. }) => Ok(self.exprs.ret(inner)),
            Some(ctx) => Ok(self.exprs.block(
                [
                    ir::Statement::Expression(
                        self.exprs.assign(
                            self.exprs
                                .local(ctx.return_local, self.return_type.unwrap()),
                            inner,
                        ),
                    ),
                    ir::Statement::Expression(self.exprs.goto(ctx.return_label)),
                ],
                self.exprs.unreachable(),
            )),
        }
    }

    fn lower_return(
        &mut self,
        inner: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.return_type.is_none() {
            return Err(CodeErrorKind::NotInAFunctionScope).with_no_span();
        }

        let inner = inner
            .map(|inner| self.lower_expr(inner, self.return_type))
            .transpose()?
            .unwrap_or_else(|| {
                self.exprs
                    .void(self.types.builtin(BuiltinType::Void), ir::ValueType::RValue)
            });

        self.make_return(inner)
    }

    fn lower_defer(
        &mut self,
        inner: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.return_type.is_none() {
            return Err(CodeErrorKind::NotInAFunctionScope).with_no_span();
        }

        if !self.loop_contexts.is_empty() {
            self.mono_ctx.diag_ctx.add_warning(CodeError {
                kind: CodeErrorKind::DeferInALoop,
                backtrace: inner.span.iter().map(|s| Marker::Span(*s)).collect(),
            })
        }

        match self.defer_context.as_mut() {
            None => {
                let mut ctx =
                    DeferContext::new(self.mono_ctx.ir.make_id(), self.mono_ctx.ir.make_id());
                ctx.in_defer = true;
                self.local_defs.push(ir::LocalDef {
                    id: ctx.return_local,
                    typ: self.return_type.unwrap(),
                });
                self.defer_context = Some(ctx);
            }
            Some(ctx) if ctx.in_defer => return Err(CodeErrorKind::DeferInDefer).with_no_span(),
            Some(ctx) => ctx.in_defer = true,
        };

        // cannot have defer_context borrowed over this point
        let inner = self.lower_expr(inner, None);
        let defer_context = self.defer_context.as_mut().unwrap();
        defer_context.in_defer = false;
        let inner = inner?;

        let defer_flag = self.mono_ctx.ir.make_id();
        self.local_defs.push(ir::LocalDef {
            id: defer_flag,
            typ: self.types.builtin(BuiltinType::Bool),
        });

        defer_context.defered.push((defer_flag, inner));
        Ok(self.exprs.assign(
            self.exprs
                .local(defer_flag, self.types.builtin(BuiltinType::Bool)),
            self.exprs
                .lit(Lit::Bool(true), self.types.builtin(BuiltinType::Bool)),
        ))
    }

    fn lower_struct_expression(
        &mut self,
        typ: ast::TyP<'ast>,
        inits: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item = self.try_resolve_struct(typ, inits, type_hint)?;

        let field_map = self.get_struct_field_map(item);
        let lowered = inits
            .iter()
            .map(|f| match field_map.get(&f.name) {
                Some(field) => self
                    .lower_expr(f.value, Some(field.ty))
                    .and_then(|e| self.try_coerce(field.ty, e))
                    .map(|i| (*field, i)),
                None => Err(CodeErrorKind::UnresolvedItem(f.name.to_string())).with_span(f.span),
            })
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|(_, e)| e.diverges()) {
            return Ok(self.exprs.diverges(lowered.into_iter().map(|(_, e)| e)));
        }

        let struct_type = self.types.named(item);

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.exprs.local(temporary, struct_type);
        self.local_defs.push(ir::LocalDef {
            id: temporary,
            typ: struct_type,
        });

        let statements = lowered
            .into_iter()
            .map(|(f, e)| {
                ir::Statement::Expression(self.exprs.assign(self.exprs.field(local, f.id, f.ty), e))
            })
            .collect::<Vec<_>>();

        Ok(self.exprs.block(statements, local))
    }

    fn lower_array_expression(
        &mut self,
        elements: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let element_type_hint = match type_hint {
            Some(ir::Ty::Array(item, _)) => Some(*item),
            _ => None,
        };

        let mut first_elem_type = None;
        let mut lowered = Vec::new();
        for expr in elements {
            let expr = self.lower_expr(expr, first_elem_type.or(element_type_hint))?;
            if let None = first_elem_type {
                let qualified = self.try_qualify_type(expr.ty)?;
                first_elem_type = Some(qualified);
            }
            lowered.push(self.try_coerce(first_elem_type.unwrap(), expr)?);
        }

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(lowered.into_iter()));
        }

        let element_type = first_elem_type.or(element_type_hint);
        let array_type = match element_type {
            Some(element_type) => self.types.array(element_type, elements.len()),
            None => return Err(CodeErrorKind::TypeInferenceFailed).with_no_span(),
        };

        let temporary = self.mono_ctx.ir.make_id();
        let local = self.exprs.local(temporary, array_type);
        self.local_defs.push(ir::LocalDef {
            id: temporary,
            typ: array_type,
        });

        let statements = lowered
            .into_iter()
            .enumerate()
            .map(|(idx, e)| {
                ir::Statement::Expression(self.exprs.assign(self.exprs.const_index(local, idx), e))
            })
            .collect::<Vec<_>>();

        Ok(self.exprs.block(statements, local))
    }

    fn lower_enum_value(
        &mut self,
        typ: ast::ItemP<'ast>,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.monomorphize_item(MonomorphizeKey(typ, &[]))?;
        let ir_id = self.mono_ctx.map_id(id);
        let result = match item_cell.try_get() {
            Some(ir::IRItem::Enum(item)) => {
                let typ = self.types.named(item_cell);
                self.exprs.cast(
                    item.members.iter().find(|v| v.id == ir_id).unwrap().value,
                    typ,
                )
            }
            _ => return Err(CodeErrorKind::CycleDetected).with_no_span(),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_expr(
        &mut self,
        expr: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let result = match &expr.kind {
            ast::ExprKind::Void => Ok(self
                .exprs
                .void(self.types.builtin(BuiltinType::Void), ValueType::RValue)),
            ast::ExprKind::Block(statements, ret) => self.lower_block(statements, ret, type_hint),
            ast::ExprKind::Lit(lit) => self.lower_lit(lit, type_hint),
            ast::ExprKind::Deref(expr) => self.lower_deref(expr, type_hint),
            ast::ExprKind::Ref(expr) => self.lower_ref(expr, type_hint),
            ast::ExprKind::Local(id) => self.lower_local(*id, type_hint),
            ast::ExprKind::Unary(op, inner) => self.lower_unary(*op, inner, type_hint),
            ast::ExprKind::Assign(lhs, rhs) => self.lower_assign(lhs, rhs, type_hint),
            ast::ExprKind::If(cond, then, els) => self.lower_if(cond, then, els, type_hint),
            ast::ExprKind::Cast(expr, typ) => self.lower_cast(expr, typ, type_hint),
            ast::ExprKind::Loop(body) => self.lower_loop(body, type_hint),
            ast::ExprKind::Binary(op, lhs, rhs) => self.lower_binary(*op, lhs, rhs, type_hint),
            ast::ExprKind::AssignOp(op, lhs, rhs) => self.lower_assign_op(*op, lhs, rhs, type_hint),
            ast::ExprKind::Break(value) => self.lower_break(*value, type_hint),
            ast::ExprKind::Defer(value) => self.lower_defer(*value, type_hint),
            ast::ExprKind::Continue => self.lower_continue(type_hint),
            ast::ExprKind::Tuple(exprs) => self.lower_tuple(exprs, type_hint),
            ast::ExprKind::TupleIndex(tup, index) => self.lower_tuple_index(tup, *index, type_hint),
            ast::ExprKind::Field(tup, field, _) => self.lower_field(tup, field, type_hint),
            ast::ExprKind::Call(func, args) => self.lower_call(func, args, type_hint),
            ast::ExprKind::Array(elements) => self.lower_array_expression(elements, type_hint),
            ast::ExprKind::EnumValue(typ, id) => self.lower_enum_value(typ, *id, type_hint),
            ast::ExprKind::Struct(func, initializers) => {
                self.lower_struct_expression(func, initializers, type_hint)
            }
            ast::ExprKind::Index(inner, index) => self.lower_index(inner, index, type_hint),
            ast::ExprKind::RangeIndex(inner, lower, upper) => {
                self.lower_range_index(inner, *lower, *upper, type_hint)
            }
            ast::ExprKind::Return(inner) => self.lower_return(*inner, type_hint),
            ast::ExprKind::Fn(item, args) => self.lower_fn(item.clone(), *args, type_hint),
            ast::ExprKind::Static(item) => self.lower_static(*item, type_hint),
            ast::ExprKind::Const(item) => self.lower_const(*item, type_hint),

            ast::ExprKind::EtCetera(_) => panic!("macros should have been expanded by now"),
            ast::ExprKind::DeferedMacro(_, _) => panic!("macros should have been expanded by now"),
        };

        result.append_span(expr.span)
    }
}
