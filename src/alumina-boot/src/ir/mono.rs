use crate::ast::lang::LangItemKind;
use crate::ast::rebind::Rebinder;
use crate::ast::{Attribute, BuiltinType, Span, TestMetadata};
use crate::common::{
    ice, AluminaError, ArenaAllocatable, CodeErrorKind, CycleGuardian, HashMap, HashSet, Marker,
};
use crate::diagnostics::DiagnosticsStack;
use crate::global_ctx::GlobalCtx;
use crate::intrinsics::{IntrinsicKind, IntrinsicValueKind};
use crate::ir::builder::{ExpressionBuilder, TypeBuilder};
use crate::ir::const_eval::{numeric_of_kind, Value};
use crate::ir::elide_zst::ZstElider;
use crate::ir::infer::TypeInferer;
use crate::ir::inline::IrInliner;
use crate::ir::lang::LangTypeKind;
use crate::ir::{FuncBody, IRItemP, LocalDef, ValueType};
use crate::name_resolution::scope::BoundItemType;
use crate::{ast, ir};

use backtrace::Backtrace;
use once_cell::unsync::OnceCell;

use std::collections::hash_map::Entry;
use std::iter::{once, repeat};
use std::rc::Rc;

use super::layout::Layouter;

macro_rules! mismatch {
    ($self:expr, $expected:literal, $actual:expr) => {
        $self.diag.err(crate::common::CodeErrorKind::TypeMismatch(
            format!("{}", $expected),
            $self.mono_ctx.type_name($actual).unwrap(),
        ))
    };

    ($self:expr, $expected:expr, $actual:expr) => {
        $self.diag.err(crate::common::CodeErrorKind::TypeMismatch(
            $self.mono_ctx.type_name($expected).unwrap(),
            $self.mono_ctx.type_name($actual).unwrap(),
        ))
    };
}

#[derive(Default)]
pub struct Caches<'ast, 'ir> {
    associated_fns: HashMap<ir::TyP<'ir>, Rc<HashMap<&'ast str, ast::ItemP<'ast>>>>,
    associated_fns_ast: HashMap<ast::TyP<'ast>, Rc<HashMap<&'ast str, ast::ItemP<'ast>>>>,
    struct_field_maps: HashMap<ir::IRItemP<'ir>, Rc<HashMap<&'ast str, &'ir ir::Field<'ir>>>>,
    protocol_bound_matches: HashMap<(ir::TyP<'ir>, ir::TyP<'ir>), BoundCheckResult>,
}

pub struct MonoCtx<'ast, 'ir> {
    ast: &'ast ast::AstCtx<'ast>,
    ir: &'ir ir::IrCtx<'ir>,
    layouter: Layouter<'ir>,
    global_ctx: GlobalCtx,
    id_map: HashMap<ast::AstId, ir::IrId>,
    cycle_guardian: CycleGuardian<(ast::ItemP<'ast>, &'ir [ir::TyP<'ir>])>,
    finished: HashMap<MonoKey<'ast, 'ir>, ir::IRItemP<'ir>>,
    reverse_map: HashMap<ir::IRItemP<'ir>, MonoKey<'ast, 'ir>>,
    tests: HashMap<ir::IRItemP<'ir>, TestMetadata<'ast>>,
    static_local_defs: HashMap<ir::IRItemP<'ir>, Vec<LocalDef<'ir>>>,
    vtable_layouts: HashMap<&'ir [ir::TyP<'ir>], ir::VtableLayout<'ir>>,
    static_inits: Vec<ir::IRItemP<'ir>>,
    caches: Caches<'ast, 'ir>,
}

#[derive(Clone)]
enum BoundCheckResult {
    Matches,
    DoesNotMatch,
    DoesNotMatchBecause(String),
}

impl<'ast, 'ir> MonoCtx<'ast, 'ir> {
    pub fn new(
        ast: &'ast ast::AstCtx<'ast>,
        ir: &'ir ir::IrCtx<'ir>,
        global_ctx: GlobalCtx,
    ) -> Self {
        MonoCtx {
            ast,
            ir,
            layouter: Layouter::new(global_ctx.clone()),
            global_ctx: global_ctx.clone(),
            id_map: HashMap::default(),
            finished: HashMap::default(),
            reverse_map: HashMap::default(),
            static_local_defs: HashMap::default(),
            cycle_guardian: CycleGuardian::new(),
            tests: HashMap::default(),
            vtable_layouts: HashMap::default(),
            static_inits: Vec::new(),
            caches: Caches::default(),
        }
    }

    fn map_id(&mut self, id: ast::AstId) -> ir::IrId {
        *self.id_map.entry(id).or_insert_with(|| self.ir.make_id())
    }

    pub fn reverse_lookup(&self, item: ir::IRItemP<'ir>) -> MonoKey<'ast, 'ir> {
        self.reverse_map
            .get(&item)
            .cloned()
            .expect("reverse lookup failed")
    }

    pub fn get_lang_type_kind(&self, typ: ir::TyP<'ir>) -> Option<LangTypeKind<'ir>> {
        let item = match typ {
            ir::Ty::Item(item) => item,
            _ => return None,
        };

        let item = self.reverse_lookup(item);
        if self.ast.lang_item(LangItemKind::Slice).ok() == Some(item.0) {
            return Some(LangTypeKind::Slice(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::RangeFull).ok() == Some(item.0) {
            return Some(LangTypeKind::Range(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::RangeFrom).ok() == Some(item.0) {
            return Some(LangTypeKind::Range(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::RangeTo).ok() == Some(item.0) {
            return Some(LangTypeKind::Range(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::RangeToInclusive).ok() == Some(item.0) {
            return Some(LangTypeKind::Range(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::Range).ok() == Some(item.0) {
            return Some(LangTypeKind::Range(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::RangeInclusive).ok() == Some(item.0) {
            return Some(LangTypeKind::Range(item.1[0]));
        }

        if self.ast.lang_item(LangItemKind::Dyn).ok() == Some(item.0) {
            return Some(LangTypeKind::Dyn(item.1[0], item.1[1]));
        }

        if self.ast.lang_item(LangItemKind::DynSelf).ok() == Some(item.0) {
            return Some(LangTypeKind::DynSelf);
        }

        if self.ast.lang_item(LangItemKind::ProtoCallable).ok() == Some(item.0) {
            if let ir::Ty::Tuple(args) = item.1[0] {
                return Some(LangTypeKind::ProtoCallable(
                    args,
                    item.1
                        .get(1)
                        .copied()
                        .unwrap_or_else(|| self.ir.intern_type(ir::Ty::void())),
                ));
            }
        }

        None
    }

    pub fn type_name(&self, typ: ir::TyP<'ir>) -> Result<String, AluminaError> {
        use ir::Ty::*;
        use std::fmt::Write;

        let mut f = String::new();

        match typ {
            Item(cell) => {
                let MonoKey(cell, args, _, _) = self.reverse_lookup(cell);

                match self.get_lang_type_kind(typ) {
                    Some(LangTypeKind::Dyn(
                        ir::Ty::Tuple(protos),
                        ir::Ty::Pointer(_, is_const),
                    )) => {
                        if *is_const {
                            let _ = write!(f, "&dyn ");
                        } else {
                            let _ = write!(f, "&mut dyn ");
                        }

                        if protos.len() > 1 {
                            let _ = write!(f, "(");
                        }

                        for (idx, arg) in protos.iter().enumerate() {
                            if idx > 0 {
                                let _ = write!(f, " + {}", self.type_name(arg)?);
                            } else {
                                let _ = write!(f, "{}", self.type_name(arg)?);
                            }
                        }

                        if protos.len() > 1 {
                            let _ = write!(f, ")");
                        }
                        return Ok(f);
                    }

                    Some(LangTypeKind::Slice(ir::Ty::Pointer(inner, is_const))) => {
                        if *is_const {
                            let _ = write!(f, "&[{}]", self.type_name(inner)?);
                        } else {
                            let _ = write!(f, "&mut [{}]", self.type_name(inner)?);
                        }
                        return Ok(f);
                    }

                    Some(LangTypeKind::ProtoCallable(args, ret)) => {
                        let _ = write!(f, "Fn(");
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                let _ = write!(f, ", ");
                            }
                            let _ = write!(f, "{}", self.type_name(arg)?);
                        }
                        let _ = write!(f, ")");
                        if !ret.is_void() {
                            let _ = write!(f, " -> {}", self.type_name(ret)?);
                        }
                        return Ok(f);
                    }
                    _ => {}
                }

                let _ = match cell.get() {
                    ast::Item::Enum(e) => write!(f, "{}", e.name.unwrap_or("{{anonymous}}")),
                    ast::Item::StructLike(e) => write!(f, "{}", e.name.unwrap_or("{{anonymous}}")),
                    ast::Item::Protocol(e) => write!(f, "{}", e.name.unwrap_or("{{anonymous}}")),
                    ast::Item::Function(e) => write!(f, "{}", e.name.unwrap_or("{{anonymous}}")),
                    ast::Item::TypeDef(e) => write!(f, "{}", e.name.unwrap_or("{{anonymous}}")),
                    _ => unreachable!(),
                };

                if !args.is_empty() {
                    let _ = write!(f, "<");
                    for (idx, arg) in args.iter().enumerate() {
                        if idx > 0 {
                            let _ = write!(f, ", {}", self.type_name(arg)?);
                        } else {
                            let _ = write!(f, "{}", self.type_name(arg)?);
                        }
                    }
                    let _ = write!(f, ">");
                }
            }

            Builtin(builtin) => {
                let _ = match builtin {
                    BuiltinType::Never => write!(f, "!"),
                    BuiltinType::Bool => write!(f, "bool"),
                    BuiltinType::U8 => write!(f, "u8"),
                    BuiltinType::U16 => write!(f, "u16"),
                    BuiltinType::U32 => write!(f, "u32"),
                    BuiltinType::U64 => write!(f, "u64"),
                    BuiltinType::U128 => write!(f, "u128"),
                    BuiltinType::USize => write!(f, "usize"),
                    BuiltinType::ISize => write!(f, "isize"),
                    BuiltinType::I8 => write!(f, "i8"),
                    BuiltinType::I16 => write!(f, "i16"),
                    BuiltinType::I32 => write!(f, "i32"),
                    BuiltinType::I64 => write!(f, "i64"),
                    BuiltinType::I128 => write!(f, "i128"),
                    BuiltinType::F32 => write!(f, "f32"),
                    BuiltinType::F64 => write!(f, "f64"),
                };
            }
            Pointer(ty, is_const) => {
                if *is_const {
                    let _ = write!(f, "&{}", self.type_name(ty)?);
                } else {
                    let _ = write!(f, "&mut {}", self.type_name(ty)?);
                }
            }
            Array(ty, len) => {
                let _ = write!(f, "[{}; {}]", self.type_name(ty)?, len);
            }
            Tuple(tys) => {
                let _ = write!(f, "(");
                for (i, ty) in tys.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(f, ", ");
                    }
                    let _ = write!(f, "{}", self.type_name(ty)?);
                }
                let _ = write!(f, ")");
            }
            FunctionPointer(args, ret) => {
                let _ = write!(f, "fn(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(f, ", ");
                    }
                    let _ = write!(f, "{}", self.type_name(arg)?);
                }
                let _ = write!(f, ")");
                if !ret.is_void() {
                    let _ = write!(f, " -> {}", self.type_name(ret)?);
                }
            }
        };

        Ok(f)
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

    current_item: Option<IRItemP<'ir>>,

    replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    return_type: Option<ir::TyP<'ir>>,
    loop_contexts: Vec<LoopContext<'ir>>,
    local_types: HashMap<ir::IrId, ir::TyP<'ir>>,
    local_type_hints: HashMap<ir::IrId, ir::TyP<'ir>>,
    local_defs: Vec<ir::LocalDef<'ir>>,
    defer_context: Option<DeferContext<'ir>>,
    diag: DiagnosticsStack,
    tentative: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonoKey<'ast, 'ir>(
    pub ast::ItemP<'ast>,
    pub &'ir [ir::TyP<'ir>],
    pub Option<ir::IrId>,
    pub bool,
);

impl<'ast, 'ir> MonoKey<'ast, 'ir> {
    pub fn new(
        item: ast::ItemP<'ast>,
        tys: &'ir [ir::TyP<'ir>],
        index: Option<ir::IrId>,
        tentative: bool,
    ) -> Self {
        MonoKey(item, tys, index, tentative)
    }
}

impl<'a, 'ast, 'ir> Monomorphizer<'a, 'ast, 'ir> {
    pub fn new<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        tentative: bool,
        parent_item: Option<IRItemP<'ir>>,
    ) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        let diag = mono_ctx.global_ctx.diag().clone();
        Monomorphizer {
            mono_ctx,
            replacements: HashMap::default(),
            local_types: HashMap::default(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: None,
            loop_contexts: Vec::new(),
            local_type_hints: HashMap::default(),
            local_defs: Vec::new(),
            defer_context: None,
            tentative,
            current_item: parent_item,
            diag: DiagnosticsStack::new(diag),
        }
    }

    pub fn with_replacements<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
        tentative: bool,
        parent_item: Option<IRItemP<'ir>>,
        diag_stack: DiagnosticsStack,
    ) -> Monomorphizer<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        Monomorphizer {
            mono_ctx,
            replacements,
            local_types: HashMap::default(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: None,
            loop_contexts: Vec::new(),
            local_defs: Vec::new(),
            local_type_hints: HashMap::default(),
            defer_context: None,
            tentative,
            current_item: parent_item,
            diag: diag_stack,
        }
    }

    fn monomorphize_enum(
        &mut self,
        item: ir::IRItemP<'ir>,
        en: &ast::Enum<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(en.span);

        if !generic_args.is_empty() {
            return Err(self.diag.err(CodeErrorKind::GenericParamCountMismatch(
                0,
                generic_args.len(),
            )));
        }

        let mut members = Vec::new();
        let mut child = Self::new(self.mono_ctx, self.tentative, self.current_item);
        let mut type_hint = None;
        let mut taken_values = HashSet::default();

        let (valued, non_valued): (Vec<_>, Vec<_>) =
            en.members.iter().copied().partition(|m| m.value.is_some());

        for m in valued {
            let _guard = self.diag.push_span(m.span);

            let expr = child.lower_expr(m.value.unwrap(), type_hint)?;
            match expr.ty {
                ir::Ty::Builtin(b) if b.is_integer() => {}
                _ => return Err(self.diag.err(CodeErrorKind::InvalidValueForEnumVariant)),
            };

            let value = ir::const_eval::ConstEvaluator::new(
                child.diag.fork(),
                child.mono_ctx.ir,
                child.local_types.iter().map(|(k, v)| (*k, *v)),
            )
            .const_eval(expr)?;

            if !type_hint.get_or_insert(expr.ty).assignable_from(expr.ty) {
                return Err(mismatch!(self, type_hint.unwrap(), expr.ty));
            }

            if !taken_values.insert(value) {
                return Err(self.diag.err(CodeErrorKind::DuplicateEnumMember));
            }

            members.push(ir::EnumMember {
                id: child.mono_ctx.map_id(m.id),
                name: m.name.alloc_on(child.mono_ctx.ir),
                value: child.exprs.literal(value, expr.ty, m.span),
            });
        }

        // This monstrosity to populate non-valued members with arbitrary types using
        // const-eval. It's bad, but it works.
        let kind = match type_hint.get_or_insert(child.types.builtin(BuiltinType::I32)) {
            ir::Ty::Builtin(k) => *k,
            _ => unreachable!(),
        };
        let enum_type = type_hint.unwrap();

        let mut counter = numeric_of_kind!(kind, 0);
        for m in non_valued {
            let next_non_taken = loop {
                if taken_values.insert(counter) {
                    break counter;
                }
                counter = ir::const_eval::ConstEvaluator::new(
                    child.diag.fork(),
                    child.mono_ctx.ir,
                    child.local_types.iter().map(|(k, v)| (*k, *v)),
                )
                .const_eval(
                    self.exprs.binary(
                        ast::BinOp::Plus,
                        self.exprs.literal(counter, enum_type, m.span),
                        self.exprs
                            .literal(numeric_of_kind!(kind, 1), enum_type, m.span),
                        enum_type,
                        m.span,
                    ),
                )?;
            };

            members.push(ir::EnumMember {
                id: child.mono_ctx.map_id(m.id),
                name: m.name.alloc_on(child.mono_ctx.ir),
                value: self.exprs.literal(next_non_taken, enum_type, m.span),
            });
        }

        let res = ir::IRItem::Enum(ir::Enum {
            name: en.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            underlying_type: enum_type,
            members: members.alloc_on(child.mono_ctx.ir),
        });

        item.assign(res);

        for mixin in en.mixins {
            self.expand_mixin(mixin)?;
        }

        Ok(())
    }

    fn resolve_placeholders(
        &mut self,
        placeholders: &[ast::Placeholder<'ast>],
        generic_args: &[ir::TyP<'ir>],
    ) -> Result<HashMap<ast::AstId, ir::TyP<'ir>>, AluminaError> {
        if generic_args.len() != placeholders.len() {
            return Err(self.diag.err(CodeErrorKind::GenericParamCountMismatch(
                placeholders.len(),
                generic_args.len(),
            )));
        }

        let replacements = self
            .replacements
            .iter()
            .map(|(a, b)| (*a, *b))
            .chain(
                placeholders
                    .iter()
                    .zip(generic_args.iter())
                    .map(|(&k, &v)| (k.id, v)),
            )
            .collect();

        Ok(replacements)
    }

    fn monomorphize_struct(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::StructLike<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.mono_ctx,
            replacements,
            self.tentative,
            self.current_item,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.typ)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let fields = s
            .fields
            .iter()
            .map(|f| {
                let _guard = self.diag.push_span(f.span);

                Ok(ir::Field {
                    id: child.mono_ctx.map_id(f.id),
                    ty: child.lower_type_for_value(f.typ)?,
                })
            })
            .collect::<Result<Vec<_>, AluminaError>>()?;

        let res = ir::IRItem::StructLike(ir::StructLike {
            name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            fields: fields.alloc_on(child.mono_ctx.ir),
            attributes: s.attributes.alloc_on(child.mono_ctx.ir),
            is_union: s.is_union,
        });
        item.assign(res);

        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        for mixin in s.mixins {
            self.expand_mixin(mixin)?;
        }

        Ok(())
    }

    fn monomorphize_typedef(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::TypeDef<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.mono_ctx,
            replacements,
            self.tentative,
            self.current_item,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.typ)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let target = s
            .target
            .ok_or_else(|| self.diag.err(CodeErrorKind::TypedefWithoutTarget))?;

        let inner = child.lower_type_unrestricted(target)?;

        let res = ir::IRItem::Alias(inner);
        item.assign(res);

        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        Ok(())
    }

    fn monomorphize_protocol(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::Protocol<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.mono_ctx,
            replacements,
            self.tentative,
            self.current_item,
            self.diag.fork(),
        );

        // Protocols can have their own protocol bounds, yay!
        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.typ)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let mut methods = Vec::new();
        for m in s.associated_fns {
            let fun = m.item.get_function();
            if !fun.placeholders.is_empty() {
                return Err(self.diag.err(CodeErrorKind::MixinOnlyProtocol));
            }

            let mut param_types = Vec::new();
            for p in fun.args {
                param_types.push(child.lower_type_for_value(p.typ)?);
            }
            let ret = child.lower_type_for_value(fun.return_type)?;

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

        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        Ok(())
    }

    fn check_protocol_bounds(
        &mut self,
        kind: ast::ProtocolBoundsKind,
        typ: ir::TyP<'ir>,
        bounds: Vec<(Option<ast::Span>, ir::TyP<'ir>, bool)>,
    ) -> Result<(), AluminaError> {
        if bounds.is_empty() {
            return Ok(());
        }

        let mut found = false;
        for (span, bound, negated) in bounds.iter().copied() {
            let _guard = self.diag.push_span(span);

            match self.check_protocol_bound(bound, typ)? {
                BoundCheckResult::Matches if negated => {
                    if kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    if negated {
                        return Err(self.diag.err(CodeErrorKind::ProtocolMatch(
                            self.mono_ctx.type_name(typ).unwrap(),
                            self.mono_ctx.type_name(bound).unwrap(),
                        )));
                    }
                }
                BoundCheckResult::DoesNotMatch if !negated => {
                    if kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    return Err(self.diag.err(CodeErrorKind::ProtocolMismatch(
                        self.mono_ctx.type_name(typ).unwrap(),
                        self.mono_ctx.type_name(bound).unwrap(),
                    )));
                }
                BoundCheckResult::DoesNotMatchBecause(detail) if !negated => {
                    if kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    return Err(self.diag.err(CodeErrorKind::ProtocolMismatchDetail(
                        self.mono_ctx.type_name(typ).unwrap(),
                        self.mono_ctx.type_name(bound).unwrap(),
                        detail,
                    )));
                }
                _ => {
                    found = true;
                    if kind == ast::ProtocolBoundsKind::Any {
                        break;
                    }
                }
            }
        }

        if !found {
            let _guard = self.diag.push_span(bounds[0].0);

            return Err(self.diag.err(CodeErrorKind::ProtocolMismatch(
                self.mono_ctx.type_name(typ).unwrap(),
                bounds
                    .iter()
                    .map(|(_, bound, negated)| {
                        if *negated {
                            format!("!{}", self.mono_ctx.type_name(bound).unwrap())
                        } else {
                            self.mono_ctx.type_name(bound).unwrap()
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" | "),
            )));
        }

        Ok(())
    }

    fn check_protocol_bound(
        &mut self,
        bound: ir::TyP<'ir>,
        ty: ir::TyP<'ir>,
    ) -> Result<BoundCheckResult, AluminaError> {
        if let Some(result) = self
            .mono_ctx
            .caches
            .protocol_bound_matches
            .get(&(bound, ty))
        {
            return Ok(result.clone());
        }

        let result = self.check_protocol_bound_uncached(bound, ty)?;
        self.mono_ctx
            .caches
            .protocol_bound_matches
            .insert((bound, ty), result.clone());

        Ok(result)
    }

    fn check_protocol_bound_uncached(
        &mut self,
        bound: ir::TyP<'ir>,
        ty: ir::TyP<'ir>,
    ) -> Result<BoundCheckResult, AluminaError> {
        let protocol_item = match bound {
            ir::Ty::Item(protocol) => match protocol.get() {
                Ok(ir::IRItem::Protocol(_)) => protocol,
                Err(_) => return Err(self.diag.err(CodeErrorKind::CyclicProtocolBound)),
                _ => {
                    if bound == ty {
                        return Ok(BoundCheckResult::Matches);
                    } else {
                        return Ok(BoundCheckResult::DoesNotMatch);
                    }
                }
            },
            _ => {
                if bound == ty {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
        };

        let MonoKey(ast_item, proto_generic_args, _, _) =
            self.mono_ctx.reverse_lookup(protocol_item);
        match self.mono_ctx.ast.lang_item_kind(ast_item) {
            Some(LangItemKind::ProtoZeroSized) => {
                if ty.is_zero_sized() {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
            Some(LangItemKind::ProtoTuple) => match ty {
                ir::Ty::Tuple(_) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoFloatingPoint) => match ty {
                ir::Ty::Builtin(k) if k.is_float() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoInteger) => match ty {
                ir::Ty::Builtin(k) if k.is_integer() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoNumeric) => match ty {
                ir::Ty::Builtin(k) if k.is_numeric() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoSigned) => match ty {
                ir::Ty::Builtin(k) if k.is_signed() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoUnsigned) => match ty {
                ir::Ty::Builtin(k) if k.is_integer() && !k.is_signed() => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoPrimitive) => match ty {
                ir::Ty::Builtin(_) => return Ok(BoundCheckResult::Matches),
                ir::Ty::Pointer(_, _) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoStruct) => match ty {
                ir::Ty::Item(item) => match item.get() {
                    Ok(ir::IRItem::StructLike(s)) if !s.is_union => {
                        return Ok(BoundCheckResult::Matches)
                    }
                    _ => return Ok(BoundCheckResult::DoesNotMatch),
                },
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoUnion) => match ty {
                ir::Ty::Item(item) => match item.get() {
                    Ok(ir::IRItem::StructLike(s)) if s.is_union => {
                        return Ok(BoundCheckResult::Matches)
                    }
                    _ => return Ok(BoundCheckResult::DoesNotMatch),
                },
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoEnum) => match ty {
                ir::Ty::Item(item) => match item.get() {
                    Ok(ir::IRItem::Enum(_)) => return Ok(BoundCheckResult::Matches),
                    _ => return Ok(BoundCheckResult::DoesNotMatch),
                },
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoPointer) => match ty {
                ir::Ty::Pointer(_, _) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoArray) => match ty {
                ir::Ty::Array(_, _) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoRange) => match self.mono_ctx.get_lang_type_kind(ty) {
                Some(LangTypeKind::Range(_)) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoRangeOf) => match self.mono_ctx.get_lang_type_kind(ty) {
                Some(LangTypeKind::Range(k)) if k == proto_generic_args[0] => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoMeta) => match ty {
                ir::Ty::Item(item) if matches!(item.get(), Ok(ir::IRItem::Protocol(_))) => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoCallable) => {
                let proto_args = match proto_generic_args[0] {
                    ir::Ty::Tuple(args) => *args,
                    _ => unreachable!(),
                };
                let proto_ret = proto_generic_args
                    .get(1)
                    .copied()
                    .unwrap_or_else(|| self.types.void());

                let actual_args: Vec<_>;
                let (args, ret) = match ty {
                    ir::Ty::FunctionPointer(args, ret) => (*args, *ret),
                    ir::Ty::Item(item) => match item.get().map_err(|e| self.diag.err(e))? {
                        ir::IRItem::Closure(fun_item) => {
                            let fun = fun_item
                                .function
                                .get()
                                .unwrap()
                                .get_function()
                                .map_err(|e| self.diag.err(e))?;
                            actual_args = fun.args.iter().skip(1).map(|arg| arg.ty).collect();
                            (&actual_args[..], fun.return_type)
                        }
                        ir::IRItem::Function(fun) => {
                            actual_args = fun.args.iter().map(|arg| arg.ty).collect();
                            (&actual_args[..], fun.return_type)
                        }
                        _ => {
                            return Ok(BoundCheckResult::DoesNotMatchBecause(
                                "not a function".into(),
                            ))
                        }
                    },
                    _ => {
                        return Ok(BoundCheckResult::DoesNotMatchBecause(
                            "not a function".into(),
                        ))
                    }
                };

                if args.len() != proto_args.len() {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(
                        "wrong number of arguments".into(),
                    ));
                }
                for (a, b) in args.iter().zip(proto_args.iter()) {
                    if *a != *b {
                        return Ok(BoundCheckResult::DoesNotMatchBecause(
                            "argument types do not match".into(),
                        ));
                    }
                }
                if ret != proto_ret {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(
                        "return type does not match".into(),
                    ));
                }
                return Ok(BoundCheckResult::Matches);
            }
            Some(LangItemKind::ProtoNamedFunction) => match ty {
                ir::Ty::Item(item)
                    if matches!(
                        item.get().map_err(|e| self.diag.err(e))?,
                        ir::IRItem::Function(_)
                    ) =>
                {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoFunctionPointer) => match ty {
                ir::Ty::FunctionPointer(..) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoArrayOf) => match ty {
                ir::Ty::Array(k, _) if *k == proto_generic_args[0] => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoPointerOf) => match ty {
                ir::Ty::Pointer(k, _) if *k == proto_generic_args[0] => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(LangItemKind::ProtoSameLayoutAs) => {
                let ty_layout = self.mono_ctx.layouter.layout_of(ty)?;
                let arg_layout = self.mono_ctx.layouter.layout_of(proto_generic_args[0])?;

                if ty_layout.is_compatible_with(&arg_layout) {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
            Some(_) | None => {}
        };

        // `&dyn Proto<...>` always satisfies Proto<...>
        if let Some(LangTypeKind::Dyn(ir::Ty::Tuple(inner_tys), _)) =
            self.mono_ctx.get_lang_type_kind(ty)
        {
            for inner_ty in inner_tys.iter() {
                if let ir::Ty::Item(inner_proto) = inner_ty {
                    let MonoKey(inner_ast, inner_args, ..) =
                        self.mono_ctx.reverse_lookup(inner_proto);

                    if ast_item == inner_ast
                        && proto_generic_args.get(0).copied() == Some(ty)
                        && proto_generic_args.get(1..) == inner_args.get(1..)
                    {
                        return Ok(BoundCheckResult::Matches);
                    }
                }
            }
        }

        let protocol = protocol_item.get_protocol().map_err(|e| self.diag.err(e))?;
        let associated_fns = self.get_associated_fns(ty)?;

        for proto_fun in protocol.methods {
            let item = match associated_fns.get(proto_fun.name) {
                Some(fun) => fun,
                None => {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                        "missing method `{}`",
                        proto_fun.name
                    )))
                }
            };

            let candidate_fun = item.get_function();
            if candidate_fun.args.len() != proto_fun.arg_types.len() {
                return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                    "`{}` has wrong number of parameters",
                    proto_fun.name
                )));
            }

            // This is a place where type inference is kind of critical - protocol can be satisfied by a
            // generic function and we need type inference to figure out the correct generic args and there
            // is no way for the user to annotate them.
            let mut type_inferer = TypeInferer::new(
                self.mono_ctx.ast,
                self.mono_ctx,
                candidate_fun.placeholders.to_vec(),
            );

            let infer_slots = candidate_fun
                .args
                .iter()
                .zip(proto_fun.arg_types.iter())
                .map(|(p, t)| (p.typ, *t))
                .chain(once((candidate_fun.return_type, proto_fun.return_type)));

            let generic_args = match type_inferer.try_infer(None, infer_slots) {
                Some(placeholders) => placeholders,
                None => {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                        "type hint would be needed for `{}`",
                        proto_fun.name
                    )));
                }
            };

            let monomorphized = match self.monomorphize_item_uncached(
                None,
                item,
                generic_args.alloc_on(self.mono_ctx.ir),
                true,
            ) {
                Ok(mono) => mono.get_function().map_err(|e| self.diag.err(e))?,
                Err(AluminaError::CodeErrors(code))
                    if code.iter().all(|c| {
                        matches!(
                            c.kind,
                            CodeErrorKind::ProtocolMatch(_, _)
                                | CodeErrorKind::ProtocolMismatch(_, _)
                                | CodeErrorKind::ProtocolMismatchDetail(_, _, _)
                        )
                    }) =>
                {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                        "`{}` does not match the protocol bounds",
                        proto_fun.name
                    )));
                }
                Err(e) => return Err(e),
            };

            for (arg, expected) in monomorphized.args.iter().zip(proto_fun.arg_types.iter()) {
                if arg.ty != *expected {
                    return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                        "`{}` has parameters of wrong type",
                        proto_fun.name
                    )));
                }
            }

            if monomorphized.return_type != proto_fun.return_type {
                return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                    "`{}` has a wrong return type",
                    proto_fun.name
                )));
            }
        }

        Ok(BoundCheckResult::Matches)
    }

    fn monomorphize_static_or_const(
        &mut self,
        item: ir::IRItemP<'ir>,
        s: &ast::StaticOrConst<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.mono_ctx,
            replacements,
            self.tentative,
            self.current_item,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.typ)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        let typ = s.typ.map(|t| child.lower_type_for_value(t)).transpose()?;
        let mut init = s.init.map(|t| child.lower_expr(t, typ)).transpose()?;

        if s.is_const {
            let init = if let Some(typ) = typ {
                let init = init.unwrap();
                child.try_coerce(typ, init)?
            } else {
                init.unwrap()
            };

            let value = ir::const_eval::ConstEvaluator::new(
                child.diag.fork(),
                child.mono_ctx.ir,
                child.local_types.iter().map(|(k, v)| (*k, *v)),
            )
            .const_eval(init)?;

            let mut elider = ZstElider::new(child.mono_ctx.ir);
            // TODO(tibordp): check that elider didn't produce any temporary local variables.
            // It should never happen, but what do you know.
            let optimized = elider.elide_zst_expr(child.exprs.literal(value, init.ty, init.span));

            let res = ir::IRItem::Const(ir::Const {
                name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                typ: init.ty,
                init: optimized,
                value,
            });

            item.assign(res);
        } else {
            let typ = typ.or_else(|| init.map(|i| i.ty)).unwrap();
            if let Some(init) = &mut init {
                *init = child.try_coerce(typ, init)?;
            }

            let res = ir::IRItem::Static(ir::Static {
                name: s.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
                typ,
                init,
                attributes: s.attributes.alloc_on(child.mono_ctx.ir),
                r#extern: s.r#extern,
            });
            item.assign(res);
            child.mono_ctx.static_inits.push(item);
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
        signature_only: bool,
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(func.span);

        let replacements = self.resolve_placeholders(func.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.mono_ctx,
            replacements,
            self.tentative,
            self.current_item,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in func.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.typ)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let parameters = func
            .args
            .iter()
            .map(|p| {
                let param = ir::Parameter {
                    id: child.mono_ctx.map_id(p.id),
                    ty: child.lower_type_for_value(p.typ)?,
                };
                child.local_types.insert(param.id, param.ty);
                Ok(param)
            })
            .collect::<Result<Vec<_>, AluminaError>>()?;

        let return_type = child.lower_type_for_value(func.return_type)?;
        let res = ir::IRItem::Function(ir::Function {
            name: func.name.map(|n| n.alloc_on(child.mono_ctx.ir)),
            attributes: func.attributes.alloc_on(child.mono_ctx.ir),
            args: parameters.alloc_on(child.mono_ctx.ir),
            varargs: func.varargs,
            return_type,
            body: OnceCell::new(),
        });
        item.assign(res);

        // This happens after we assign the signature to avoid issues when calling recursively
        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        // We need the item to be assigned before we monomorphize the body, as the
        // function can be recursive and we need to be able to get the signature for
        // typechecking purposes.

        if signature_only {
            return Ok(());
        }

        child.return_type = Some(return_type);
        if let Some(body) = func.body {
            let body = child.lower_function_body(
                body,
                func.attributes.contains(&ast::Attribute::InlineDuringMono),
            )?;
            item.get_function().unwrap().body.set(body).unwrap();
        }

        Ok(())
    }

    // Mixin expansion shouldn't really happen here, as it onyl touches the AST and does not
    // create any IR. However, it happens here as all the AST items have surely been populated
    // by now. In the future this should probably be a separate pass.
    pub fn expand_mixin(&mut self, mixin: &ast::Mixin<'ast>) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(mixin.span);

        if mixin.contents.contents.get().is_some() {
            return Ok(());
        }

        let (protocol, generic_args) = match mixin.protocol {
            ast::Ty::Item(item) if matches!(item.get(), ast::Item::Protocol(_)) => (item, vec![]),
            ast::Ty::Generic(ast::Ty::Item(item), args)
                if matches!(item.get(), ast::Item::Protocol(_)) =>
            {
                (item, args.to_vec())
            }
            _ => {
                return Err(self
                    .diag
                    .err(CodeErrorKind::NotAProtocol(format!("{:?}", mixin.protocol))))
            }
        };

        let protocol = protocol.get_protocol();

        // TODO: Default generic args
        if protocol.placeholders.len() != generic_args.len() {
            return Err(self.diag.err(CodeErrorKind::GenericParamCountMismatch(
                protocol.placeholders.len(),
                generic_args.len(),
            )));
        }

        let mut rebinder = Rebinder::new(
            self.mono_ctx.ast,
            protocol
                .placeholders
                .iter()
                .zip(generic_args.iter())
                .map(|(a, b)| (a.id, *b))
                .collect(),
        );

        let mut result = Vec::new();

        for function in protocol.associated_fns {
            let fun = function.item.get_function();

            let placeholders = if fun.placeholders.is_empty() {
                mixin.placeholders
            } else {
                let rebound_placeholders = fun
                    .placeholders
                    .iter()
                    .map(|p| rebinder.visit_placeholder(p))
                    .collect::<Result<Vec<_>, _>>()?;

                mixin
                    .placeholders
                    .iter()
                    .copied()
                    .chain(rebound_placeholders)
                    .collect::<Vec<_>>()
                    .alloc_on(self.mono_ctx.ast)
            };

            let body = match fun.body {
                Some(body) => rebinder.visit_expr(body)?,
                None => continue,
            };

            let new_func = self.mono_ctx.ast.make_symbol();
            new_func.assign(ast::Item::Function(ast::Function {
                name: fun.name,
                attributes: fun.attributes,
                placeholders,
                return_type: rebinder.visit_typ(fun.return_type)?,
                args: fun
                    .args
                    .iter()
                    .map(|p| {
                        rebinder.visit_typ(p.typ).map(|typ| ast::Parameter {
                            id: p.id,
                            typ,
                            span: p.span,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?
                    .alloc_on(self.mono_ctx.ast),
                body: Some(body),
                span: fun.span,
                varargs: false,
                is_local: fun.is_local,
                is_protocol_fn: false,
            }));

            result.push(ast::AssociatedFn {
                name: function.name,
                item: new_func,
            })
        }

        mixin
            .contents
            .contents
            .set(result.alloc_on(self.mono_ctx.ast))
            .unwrap();

        Ok(())
    }

    pub fn lower_function_body(
        mut self,
        expr: ast::ExprP<'ast>,
        is_ir_inline: bool,
    ) -> Result<ir::FuncBody<'ir>, AluminaError> {
        let return_type = self.return_type.unwrap();
        let body = self.lower_expr(expr, Some(return_type))?;

        let body = self.try_coerce(return_type, body)?;
        if is_ir_inline {
            if self.defer_context.is_some() {
                return Err(self.diag.err(CodeErrorKind::IrInlineFlowControl));
            }
            if !self.local_defs.is_empty() {
                return Err(self.diag.err(CodeErrorKind::IrInlineLocalDefs));
            }
        };

        let mut statements = Vec::new();
        if self.defer_context.is_some() {
            self.generate_defer_prologue(&mut statements);
        }

        if let ir::ExprKind::Block(block, ret) = body.kind {
            statements.extend(block.iter().cloned());
            statements.push(ir::Statement::Expression(self.make_return(ret, None)?));
        } else {
            statements.push(ir::Statement::Expression(self.make_return(body, None)?));
        };

        if self.defer_context.is_some() {
            self.generate_defer_epilogue(&mut statements);
        }

        let function_body = FuncBody {
            statements: statements.alloc_on(self.mono_ctx.ir),
            local_defs: self.local_defs.alloc_on(self.mono_ctx.ir),
            raw_body: Some(body),
        };

        let elider = ZstElider::new(self.mono_ctx.ir);
        let optimized = elider.elide_zst_func_body(function_body);

        Ok(optimized)
    }

    pub fn get_mono_key(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
        tentative: bool,
    ) -> Result<MonoKey<'ast, 'ir>, AluminaError> {
        let mut index = None;

        if tentative {
            index = self.current_item.map(|i| i.id)
        }

        let placeholders = match item.get() {
            ast::Item::Function(f) => {
                if f.is_local {
                    index = self.current_item.map(|i| i.id);
                }
                f.placeholders
            }
            ast::Item::Protocol(p) => p.placeholders,
            ast::Item::StructLike(s) => s.placeholders,
            _ => return Ok(MonoKey::new(item, generic_args, index, tentative)),
        };

        if placeholders.len() <= generic_args.len() {
            return Ok(MonoKey::new(item, generic_args, index, tentative));
        }

        // We cannot rely on the mono_ctx.finished map to bust cyclic references in default
        // generic parameters.
        let _guard = self
            .mono_ctx
            .cycle_guardian
            .guard((item, generic_args))
            .map_err(|_| self.diag.err(CodeErrorKind::CycleDetected))?;

        let mut args: Vec<_> = generic_args.to_vec();
        for placeholder in placeholders.iter().skip(generic_args.len()) {
            let _guard = self.diag.push_span(placeholder.span);

            match placeholder.default {
                Some(typ) => {
                    args.push(self.lower_type_unrestricted(typ)?);
                }
                None => return Ok(MonoKey::new(item, generic_args, index, tentative)),
            }
        }

        Ok(MonoKey::new(
            item,
            args.alloc_on(self.mono_ctx.ir),
            index,
            tentative,
        ))
    }

    pub fn monomorphize_item(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        self.monomorphize_item_uncached(None, item, generic_args, false)
    }

    pub fn monomorphize_item_uncached(
        &mut self,
        existing_symbol: Option<IRItemP<'ir>>,
        item: ast::ItemP<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
        signature_only: bool,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        // Protocol bounds checking uses signature_only to avoid infinite recursion/unpopulated symbols,
        // make sure other cases are appropriately handled before allowing them.
        assert!(!signature_only || matches!(item.get(), ast::Item::Function(_)));

        let key = self.get_mono_key(item, generic_args, signature_only)?;

        let item: ir::IRItemP =
            existing_symbol.unwrap_or(match self.mono_ctx.finished.entry(key.clone()) {
                // The cell may be empty at this point if we are dealing with recursive references
                // In this case, we will just return the item as is, but it will not
                // be populated until the top-level item is finished.
                Entry::Occupied(entry) => {
                    if entry.get().get().is_err() {
                        match key.0.get() {
                            ast::Item::StaticOrConst(_) => {
                                return Err(self
                                    .diag
                                    .err(CodeErrorKind::RecursiveStaticInitialization))
                            }
                            _ => {}
                        }
                    }
                    return Ok(entry.get());
                }
                Entry::Vacant(entry) => {
                    let symbol = self.mono_ctx.ir.make_symbol();
                    self.mono_ctx.reverse_map.insert(symbol, key.clone());
                    entry.insert(symbol)
                }
            });

        let old_item = std::mem::replace(&mut self.current_item, Some(item));
        let ret = self.monomorphize_item_type(key, item, signature_only);
        self.current_item = old_item;
        ret?;

        Ok(item)
    }

    pub fn monomorphize_item_type(
        &mut self,
        key: MonoKey<'ast, 'ir>,
        item: ir::IRItemP<'ir>,
        signature_only: bool,
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push(Marker::Monomorphization);

        match key.0.get() {
            ast::Item::Enum(en) => {
                self.monomorphize_enum(item, en, key.1)?;
            }
            ast::Item::Function(func) => {
                self.monomorphize_function(item, func, key.1, signature_only)?;

                if !self.tentative && func.attributes.contains(&ast::Attribute::Test) {
                    let fun = item.get_function().unwrap();
                    if !fun.args.is_empty() || fun.return_type != self.types.void() {
                        return Err(self.diag.err(CodeErrorKind::InvalidTestCaseSignature));
                    }

                    let metadata = self.mono_ctx.ast.test_metadata(key.0).unwrap();
                    self.mono_ctx.tests.insert(item, metadata);
                }
            }
            ast::Item::StructLike(s) => {
                self.monomorphize_struct(item, s, key.1)?;
            }
            ast::Item::StaticOrConst(s) => {
                self.monomorphize_static_or_const(item, s, key.1)?;
            }
            ast::Item::Macro(_) => {
                ice!("macros should have been expanded by now");
            }
            ast::Item::BuiltinMacro(_) => {
                ice!("macros should have been expanded by now");
            }
            ast::Item::Intrinsic(_) => {
                ice!("intrinsics shouldn't be monomorphized");
            }
            ast::Item::Protocol(p) => {
                self.monomorphize_protocol(item, p, key.1)?;
            }
            ast::Item::TypeDef(i) => {
                self.monomorphize_typedef(item, i, key.1)?;
            }
        };

        Ok(())
    }

    pub fn generate_static_constructor(
        &mut self,
        alive: &HashSet<IRItemP<'ir>>,
    ) -> Result<IRItemP<'ir>, AluminaError> {
        let item = self.mono_ctx.ir.make_symbol();
        self.return_type = Some(self.types.void());

        let mut statements = Vec::new();
        let mut local_defs = Vec::new();

        for (v, s) in self
            .mono_ctx
            .static_inits
            .iter()
            .filter_map(|v| match v.get() {
                Ok(ir::IRItem::Static(s)) if s.init.is_some() && alive.contains(v) => Some((v, s)),
                _ => None,
            })
        {
            local_defs.extend(self.mono_ctx.static_local_defs.get(v).unwrap());
            let init = s.init.unwrap();
            if init.diverges() {
                statements.push(ir::Statement::Expression(init));
                break;
            } else {
                statements.push(ir::Statement::Expression(self.exprs.assign(
                    self.exprs.static_var(v, s.typ, init.span),
                    s.init.unwrap(),
                    init.span,
                )));
            }
        }

        let body = self.exprs.block(
            statements,
            self.exprs
                .void(self.types.void(), ir::ValueType::RValue, None),
            None,
        );

        let mut statements = Vec::new();
        if let ir::ExprKind::Block(block, ret) = body.kind {
            statements.extend(block.iter().cloned());
            statements.push(ir::Statement::Expression(self.make_return(ret, None)?));
        } else {
            statements.push(ir::Statement::Expression(self.make_return(body, None)?));
        };

        let function_body = FuncBody {
            statements: statements.alloc_on(self.mono_ctx.ir),
            local_defs: local_defs.alloc_on(self.mono_ctx.ir),
            raw_body: None,
        };

        let elider = ZstElider::new(self.mono_ctx.ir);
        let optimized = elider.elide_zst_func_body(function_body);

        item.assign(ir::IRItem::Function(ir::Function {
            name: None,
            attributes: [Attribute::StaticConstructor].alloc_on(self.mono_ctx.ir),
            args: [].alloc_on(self.mono_ctx.ir),
            return_type: self.types.void(),
            varargs: false,
            body: OnceCell::from(optimized),
        }));

        Ok(item)
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
        let item = self
            .mono_ctx
            .ast
            .lang_item(kind)
            .map_err(|e| self.diag.err(e))?;
        let args = self.mono_ctx.ir.arena.alloc_slice_fill_iter(generic_args);
        self.monomorphize_item(item, args)
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

    pub fn lower_type_for_value(
        &mut self,
        typ: ast::TyP<'ast>,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        let typ = self.lower_type_unrestricted(typ)?;

        // Protocols themselves can be used as types in certain blessed scenarios (e.g. intrinsics, `dyn` object),
        // but they don't work as proper types for values (similar to upcoming extern types).
        // `let a: Proto;` makes no sense, even though a protocol can be used as a generic parameter to an item to
        // ensure a unique monomorphized version for each distinct protocol.
        if let ir::Ty::Item(item) = typ {
            if let Ok(ir::IRItem::Protocol(_)) = item.get() {
                return Err(self.diag.err(CodeErrorKind::ProtocolsAreSpecialMkay(
                    self.mono_ctx.type_name(typ).unwrap(),
                )));
            }
        }

        Ok(typ)
    }

    // Builtin type operators
    fn try_lower_type_operator(
        &mut self,
        ast_item: ast::ItemP<'ast>,
        args: &[ir::TyP<'ir>],
    ) -> Result<Option<ir::TyP<'ir>>, AluminaError> {
        macro_rules! arg_count {
            ($count:expr) => {
                if args.len() != $count {
                    return Err(self.diag.err(CodeErrorKind::InvalidTypeOperator));
                }
            };
        }

        match self.mono_ctx.ast.lang_item_kind(ast_item) {
            Some(LangItemKind::TypeopPointerWithMutOf) => {
                arg_count!(2);
                if let ir::Ty::Pointer(_, is_const) = args[1] {
                    return Ok(Some(self.types.pointer(args[0], *is_const)));
                }
            }
            Some(LangItemKind::TypeopArrayWithLengthOf) => {
                arg_count!(2);
                if let ir::Ty::Array(_, len) = args[1] {
                    return Ok(Some(self.types.array(args[0], *len)));
                }
            }
            Some(LangItemKind::TypeopTupleHeadOf) => {
                arg_count!(1);
                if let ir::Ty::Tuple(tys) = args[0] {
                    if !tys.is_empty() {
                        return Ok(Some(tys[0]));
                    }
                }
            }
            Some(LangItemKind::TypeopTupleTailOf) => {
                arg_count!(1);
                if let ir::Ty::Tuple(tys) = args[0] {
                    match tys.len() {
                        0 => {}
                        1 => return Ok(Some(self.types.void())),
                        _ => {
                            return Ok(Some(self.mono_ctx.ir.intern_type(ir::Ty::Tuple(&tys[1..]))))
                        }
                    }
                }
                return Err(self.diag.err(CodeErrorKind::InvalidTypeOperator));
            }
            Some(LangItemKind::TypeopGenericArgsOf) => {
                arg_count!(1);
                match args[0] {
                    ir::Ty::Item(cell) => {
                        let MonoKey(_, types, _, _) = self.mono_ctx.reverse_lookup(cell);
                        if types.is_empty() {
                            return Ok(Some(self.types.void()));
                        } else {
                            return Ok(Some(self.types.tuple(types.iter().copied())));
                        }
                    }
                    _ => {}
                }
                return Err(self.diag.err(CodeErrorKind::InvalidTypeOperator));
            }
            Some(LangItemKind::TypeopReturnTypeOf) => {
                arg_count!(1);
                if let ir::Ty::FunctionPointer(_, ret) = args[0] {
                    return Ok(Some(*ret));
                }
                if let ir::Ty::Item(f) = args[0] {
                    match f.get().map_err(|e| self.diag.err(e))? {
                        ir::IRItem::Function(f) => {
                            return Ok(Some(f.return_type));
                        }
                        ir::IRItem::Closure(c) => {
                            return Ok(Some(
                                c.function
                                    .get()
                                    .unwrap()
                                    .get_function()
                                    .map_err(|e| self.diag.err(e))?
                                    .return_type,
                            ));
                        }
                        _ => {}
                    }
                }
            }
            Some(LangItemKind::TypeopArgumentsOf) => {
                arg_count!(1);
                if let ir::Ty::FunctionPointer(args, _) = args[0] {
                    return Ok(Some(self.types.tuple(args.iter().copied())));
                }

                if let ir::Ty::Item(f) = args[0] {
                    match f.get().map_err(|e| self.diag.err(e))? {
                        ir::IRItem::Function(f) => {
                            return Ok(Some(self.types.tuple(f.args.iter().map(|a| a.ty))));
                        }
                        ir::IRItem::Closure(c) => {
                            return Ok(Some(
                                self.types.tuple(
                                    c.function
                                        .get()
                                        .unwrap()
                                        .get_function()
                                        .map_err(|e| self.diag.err(e))?
                                        .args
                                        .iter()
                                        .map(|a| a.ty)
                                        .skip(1),
                                ),
                            ));
                        }
                        _ => {}
                    }
                }
            }
            Some(LangItemKind::TypeopEnumTypeOf) => {
                arg_count!(1);
                if let ir::Ty::Item(e) = args[0] {
                    if let Ok(e) = e.get_enum() {
                        return Ok(Some(e.underlying_type));
                    }
                }
            }
            _ => return Ok(None),
        };

        Err(self.diag.err(CodeErrorKind::InvalidTypeOperator))
    }

    fn lower_type_unrestricted(
        &mut self,
        typ: ast::TyP<'ast>,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *typ {
            ast::Ty::Builtin(kind) => self.types.builtin(kind),
            ast::Ty::Array(inner, len) => {
                let inner = self.lower_type_for_value(inner)?;
                let mut child = self.make_tentative_child();
                let len_expr =
                    child.lower_expr(len, Some(child.types.builtin(BuiltinType::USize)))?;
                let len = ir::const_eval::ConstEvaluator::new(
                    child.diag.fork(),
                    child.mono_ctx.ir,
                    child.local_types.iter().map(|(k, v)| (*k, *v)),
                )
                .const_eval(len_expr)
                .and_then(|v| match v {
                    Value::USize(v) => Ok(v),
                    _ => Err(mismatch!(
                        self,
                        self.types.builtin(BuiltinType::USize),
                        len_expr.ty
                    )),
                })?;

                self.types.array(inner, len)
            }
            ast::Ty::Pointer(inner, is_const) => {
                let inner = self.lower_type_for_value(inner)?;
                self.types.pointer(inner, is_const)
            }
            ast::Ty::Slice(inner, is_const) => {
                let inner = self.lower_type_for_value(inner)?;
                self.slice_of(inner, is_const)?
            }
            ast::Ty::FunctionPointer(args, ret) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower_type_for_value(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = self.lower_type_for_value(ret)?;
                self.types.function(args, ret)
            }
            ast::Ty::FunctionProtocol(args, ret) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower_type_for_value(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = self.lower_type_for_value(ret)?;

                let item = self.monomorphize_lang_item(
                    LangItemKind::ProtoCallable,
                    [self.types.tuple(args), ret],
                )?;
                self.types.named(item)
            }
            ast::Ty::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|arg| self.lower_type_for_value(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                self.types.tuple(items)
            }
            ast::Ty::Placeholder(id) => self.replacements.get(&id).copied().ok_or_else(|| {
                self.diag.err(CodeErrorKind::InternalError(
                    "unbound placeholder".to_string(),
                    Backtrace::new().into(),
                ))
            })?,
            ast::Ty::Item(item) => match self.mono_ctx.ast.lang_item_kind(item) {
                Some(LangItemKind::ImplBuiltin(kind)) => self.types.builtin(kind),
                Some(LangItemKind::ImplArray | LangItemKind::ImplTuple(..)) => {
                    return Err(self.diag.err(CodeErrorKind::BuiltinTypesAreSpecialMkay));
                }
                _ => {
                    let item = self.monomorphize_item(item, &[])?;
                    if let Some(typ) = item.get_alias() {
                        return Ok(typ);
                    }

                    self.types.named(item)
                }
            },
            ast::Ty::Generic(inner, args) => {
                let item = match inner {
                    ast::Ty::Item(item) => item,
                    ast::Ty::Defered(spec) => self.resolve_defered_func(spec)?,
                    _ => ice!("unsupported generic type"),
                };

                let args = args
                    .iter()
                    .map(|arg| self.lower_type_unrestricted(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir);

                if let Some(ty) = self.try_lower_type_operator(item, args)? {
                    return Ok(ty);
                }

                let ir_item = self.monomorphize_item(item, args)?;
                if let Some(typ) = ir_item.get_alias() {
                    return Ok(typ);
                }

                match item.get() {
                    ast::Item::Protocol(_) => self.types.named(ir_item),
                    ast::Item::Function(_) => self.types.named(ir_item),
                    _ => self.types.named(ir_item),
                }
            }
            ast::Ty::Defered(def) => {
                // Currently there are no associated types, so this must be a function
                let item = self.resolve_defered_func(&def)?;
                let ir_item = self.monomorphize_item(item, &[])?;
                self.types.named(ir_item)
            }
            ast::Ty::Dyn(inner, is_const) => {
                let protocols: Vec<_> = inner
                    .iter()
                    .map(|t| self.lower_type_unrestricted(t))
                    .collect::<Result<_, AluminaError>>()?;

                let mut protocol_items = Vec::new();
                for protocol in protocols.iter() {
                    match protocol {
                        ir::Ty::Item(protocol_item)
                            if matches!(
                                protocol_item.get().map_err(|e| self.diag.err(e))?,
                                ir::IRItem::Protocol(_)
                            ) =>
                        {
                            let MonoKey(ast_item, _, _, _) =
                                self.mono_ctx.reverse_lookup(protocol_item);

                            if let Some(p) = self.mono_ctx.ast.lang_item_kind(ast_item) {
                                if p.is_builtin_protocol() {
                                    return Err(self.diag.err(CodeErrorKind::BuiltinProtocolDyn));
                                }
                            }

                            protocol_items.push(*protocol_item)
                        }
                        _ => return Err(self.diag.err(CodeErrorKind::NonProtocolDyn)),
                    };
                }

                let key = protocols.alloc_on(self.mono_ctx.ir);
                let key_ty = self.mono_ctx.ir.intern_type(ir::Ty::Tuple(key));

                let ptr_type = self.types.pointer(self.types.void(), is_const);
                let item = self.monomorphize_lang_item(LangItemKind::Dyn, [key_ty, ptr_type])?;

                self.create_vtable_layout(key)?;

                self.types.named(item)
            }
            ast::Ty::TypeOf(inner) => {
                let mut child = self.make_tentative_child();
                let expr = child.lower_expr(inner, None)?;
                expr.ty
            }
            ast::Ty::When(cond, then, els) => {
                // Do not move outside the branch, this must evaluate lazily as the non-matching
                // branch may contain a compile error.
                if self.static_cond_matches(&cond)? {
                    self.lower_type_unrestricted(then)?
                } else {
                    self.lower_type_unrestricted(els)?
                }
            }
        };

        Ok(result)
    }

    fn dyn_self(&mut self) -> Result<ir::TyP<'ir>, AluminaError> {
        let ret = self.monomorphize_lang_item(LangItemKind::DynSelf, [])?;
        Ok(self.types.named(ret))
    }

    fn contains_type(&self, haystack: ir::TyP<'ir>, needle: ir::TyP<'ir>) -> bool {
        if haystack == needle {
            return true;
        }

        match haystack {
            ir::Ty::Array(inner, _) | ir::Ty::Pointer(inner, _) => {
                self.contains_type(inner, needle)
            }
            ir::Ty::FunctionPointer(args, ret) => {
                args.iter().any(|arg| self.contains_type(arg, needle))
                    || self.contains_type(ret, needle)
            }
            ir::Ty::Tuple(tys) => tys.iter().any(|ty| self.contains_type(ty, needle)),
            ir::Ty::Item(item) => match item.get().map_err(|e| self.diag.err(e)) {
                Ok(ir::IRItem::Protocol(_)) => false,
                _ => self
                    .mono_ctx
                    .reverse_lookup(item)
                    .1
                    .iter()
                    .any(|ty| self.contains_type(ty, needle)),
            },
            _ => false,
        }
    }

    fn create_vtable_layout(&mut self, protocols: &'ir [ir::TyP<'ir>]) -> Result<(), AluminaError> {
        if self.mono_ctx.vtable_layouts.contains_key(protocols) {
            return Ok(());
        }

        let dyn_self = self.dyn_self()?;
        let mut vtable_methods = Vec::new();

        for protocol_ty in protocols {
            let protocol_item = match protocol_ty {
                ir::Ty::Item(item) => item,
                _ => unreachable!(),
            };

            let protocol = protocol_item.get_protocol().map_err(|e| self.diag.err(e))?;
            for proto_fun in protocol.methods {
                macro_rules! bail {
                    () => {
                        return Err(self.diag.err(CodeErrorKind::NonDynnableFunction(
                            proto_fun.name.to_string(),
                        )))
                    };
                }

                if self.contains_type(proto_fun.return_type, dyn_self) {
                    bail!()
                }

                let args = match proto_fun.arg_types {
                    [ir::Ty::Pointer(typ, is_const), rest @ ..] => {
                        if *typ != dyn_self
                            || rest.iter().any(|ty| self.contains_type(ty, dyn_self))
                        {
                            bail!()
                        }

                        std::iter::once(self.types.pointer(self.types.void(), *is_const))
                            .chain(rest.iter().copied())
                            .collect::<Vec<_>>()
                            .alloc_on(self.mono_ctx.ir)
                    }
                    _ => bail!(),
                };

                vtable_methods.push(ir::ProtocolFunction {
                    name: proto_fun.name,
                    arg_types: args,
                    return_type: proto_fun.return_type,
                });
            }
        }

        self.mono_ctx.vtable_layouts.insert(
            protocols,
            ir::VtableLayout {
                methods: vtable_methods.alloc_on(self.mono_ctx.ir),
            },
        );

        Ok(())
    }

    fn raise_type(&mut self, typ: ir::TyP<'ir>) -> Result<ast::TyP<'ast>, AluminaError> {
        let result = match typ {
            ir::Ty::Builtin(kind) => ast::Ty::Builtin(*kind),
            ir::Ty::Array(inner, size) => {
                let inner = self.raise_type(inner)?;
                ast::Ty::Array(
                    inner,
                    ast::Expr {
                        kind: ast::ExprKind::Lit(ast::Lit::Int(
                            false,
                            *size as _,
                            Some(ast::BuiltinType::USize),
                        )),
                        span: None,
                    }
                    .alloc_on(self.mono_ctx.ast),
                )
            }
            ir::Ty::Pointer(inner, is_const) => {
                let inner = self.raise_type(inner)?;
                ast::Ty::Pointer(inner, *is_const)
            }
            ir::Ty::FunctionPointer(args, ret) => {
                let args = args
                    .iter()
                    .map(|arg| self.raise_type(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = self.raise_type(ret)?;

                ast::Ty::FunctionPointer(args.alloc_on(self.mono_ctx.ast), ret)
            }
            ir::Ty::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|arg| self.raise_type(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                ast::Ty::Tuple(items.alloc_on(self.mono_ctx.ast))
            }
            ir::Ty::Item(item) => {
                let item = self.mono_ctx.reverse_lookup(item);
                let base = match typ {
                    ir::Ty::Item(_) => ast::Ty::Item(item.0),
                    _ => unreachable!(),
                };
                if item.1.is_empty() {
                    base
                } else {
                    let args = item
                        .1
                        .iter()
                        .map(|arg| self.raise_type(arg))
                        .collect::<Result<Vec<_>, _>>()?;

                    ast::Ty::Generic(
                        self.mono_ctx.ast.intern_type(base),
                        args.alloc_on(self.mono_ctx.ast),
                    )
                }
            }
        };

        Ok(self.mono_ctx.ast.intern_type(result))
    }

    fn get_struct_field_map(
        &mut self,
        item: ir::IRItemP<'ir>,
    ) -> Result<Rc<HashMap<&'ast str, &'ir ir::Field<'ir>>>, AluminaError> {
        if let Some(map) = self.mono_ctx.caches.struct_field_maps.get(&item) {
            return Ok(map.clone());
        }

        let map = Rc::new(self.get_struct_field_map_uncached(item)?);

        self.mono_ctx
            .caches
            .struct_field_maps
            .insert(item, map.clone());

        Ok(map)
    }

    fn get_struct_field_map_uncached(
        &mut self,
        item: ir::IRItemP<'ir>,
    ) -> Result<HashMap<&'ast str, &'ir ir::Field<'ir>>, AluminaError> {
        let MonoKey(ast_item, _, _, _) = self.mono_ctx.reverse_lookup(item);
        let ir_struct = item.get_struct_like().map_err(|e| self.diag.err(e))?;
        let ast_struct = ast_item.get_struct_like();

        let res = ast_struct
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
            .collect();

        Ok(res)
    }

    fn get_associated_fns(
        &mut self,
        typ: ir::TyP<'ir>,
    ) -> Result<Rc<HashMap<&'ast str, ast::ItemP<'ast>>>, AluminaError> {
        if let Some(c) = self.mono_ctx.caches.associated_fns.get(&typ) {
            return Ok(c.clone());
        }

        let raised = self.raise_type(typ)?;
        let associated_fns = self.get_associated_fns_for_ast(raised)?;

        self.mono_ctx
            .caches
            .associated_fns
            .insert(typ, associated_fns.clone());

        Ok(associated_fns)
    }

    fn get_associated_fns_for_ast(
        &mut self,
        typ: ast::TyP<'ast>,
    ) -> Result<Rc<HashMap<&'ast str, ast::ItemP<'ast>>>, AluminaError> {
        if let Some(c) = self.mono_ctx.caches.associated_fns_ast.get(&typ) {
            return Ok(c.clone());
        }

        let associated_fns = Rc::new(self.get_associated_fns_uncached(typ)?);
        self.mono_ctx
            .caches
            .associated_fns_ast
            .insert(typ, associated_fns.clone());

        Ok(associated_fns)
    }

    fn get_associated_fns_uncached(
        &mut self,
        typ: ast::TyP<'ast>,
    ) -> Result<HashMap<&'ast str, ast::ItemP<'ast>>, AluminaError> {
        let mut associated_fns = HashMap::default();

        let item = match typ {
            ast::Ty::Builtin(kind) => self
                .mono_ctx
                .ast
                .lang_item(LangItemKind::ImplBuiltin(*kind))
                .map_err(|e| self.diag.err(e))?,
            ast::Ty::Array(_, _) => self
                .mono_ctx
                .ast
                .lang_item(LangItemKind::ImplArray)
                .map_err(|e| self.diag.err(e))?,
            ast::Ty::Tuple(items) => self
                .mono_ctx
                .ast
                .lang_item(LangItemKind::ImplTuple(items.len()))
                .map_err(|e| self.diag.err(e))?,

            ast::Ty::Item(item) => item,
            ast::Ty::Generic(ast::Ty::Item(item), _) => item,
            _ => return Ok(associated_fns),
        };

        let (fns, mixins) = match item.get() {
            ast::Item::StructLike(s) => (s.associated_fns, s.mixins),
            ast::Item::Enum(e) => (e.associated_fns, e.mixins),
            // ast::Item::TypeDef(e) => (e.),
            _ => ice!("no associated functions for this type"),
        };

        associated_fns.extend(fns.iter().map(|f| (f.name, f.item)));

        for mixin in mixins {
            let mixin_fns = match mixin.contents.contents.get() {
                Some(fns) => fns,
                None => {
                    self.expand_mixin(mixin)?;
                    mixin.contents.contents.get().unwrap()
                }
            };

            for fun in *mixin_fns {
                // Mixin functions are weaker than native associated functions, so they can be
                // shadowed. If there are multiple mixins with the same function name, the order
                // is undefined (FIXME: make it predictable somehow)
                if !associated_fns.contains_key(fun.name) {
                    associated_fns.insert(fun.name, fun.item);
                }
            }
        }

        Ok(associated_fns)
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
            local_type_hints: self.local_type_hints.clone(),
            defer_context: self.defer_context.clone(),
            current_item: self.current_item,
            tentative: true,
            diag: self.diag.fork(),
        }
    }

    fn try_coerce(
        &mut self,
        lhs_typ: ir::TyP<'ir>,
        rhs: ir::ExprP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if lhs_typ.assignable_from(rhs.ty) {
            return Ok(rhs);
        }

        match (lhs_typ, rhs.ty) {
            (ir::Ty::FunctionPointer(args, ret), ir::Ty::Item(item)) => {
                match item.get().map_err(|e| self.diag.err(e))? {
                    ir::IRItem::Function(fun) => {
                        if fun.args.len() != args.len() {
                            return Err(mismatch!(self, lhs_typ, rhs.ty));
                        }
                        // There is no co- and contra-variance, argument and return types must match
                        // exactly.
                        if fun.return_type != *ret {
                            return Err(mismatch!(self, lhs_typ, rhs.ty));
                        }
                        for (a, b) in fun.args.iter().zip(args.iter()) {
                            if a.ty != *b {
                                return Err(mismatch!(self, lhs_typ, rhs.ty));
                            }
                        }

                        // Named functions directly coerce into function pointers, cast it to avoid
                        // ZST elision issues later on.
                        let result = self.exprs.cast(rhs, lhs_typ, rhs.span);

                        return Ok(result.alloc_on(self.mono_ctx.ir));
                    }
                    ir::IRItem::Closure(_) => {
                        return Err(self.diag.err(CodeErrorKind::ClosuresAreNotFns))
                    }
                    _ => {}
                }
            }
            _ => {}
        };

        let lhs_lang = self.mono_ctx.get_lang_type_kind(lhs_typ);
        let rhs_lang = self.mono_ctx.get_lang_type_kind(rhs.ty);

        match (&lhs_lang, rhs_lang) {
            // &mut [T] -> &[T]
            (Some(LangTypeKind::Slice(t1_ptr)), Some(LangTypeKind::Slice(t2_ptr))) => {
                match (t1_ptr, t2_ptr) {
                    (ir::Ty::Pointer(t1, true), ir::Ty::Pointer(t2, _)) if t1 == t2 => {
                        let item =
                            self.monomorphize_lang_item(LangItemKind::SliceConstCoerce, [*t1])?;

                        let func = self.exprs.function(item, rhs.span);
                        return self.call(func, [rhs].into_iter(), lhs_typ, rhs.span);
                    }
                    _ => {}
                }
            }
            // &mut dyn Proto -> &dyn Proto
            (
                Some(LangTypeKind::Dyn(t1_proto, t1_ptr)),
                Some(LangTypeKind::Dyn(t2_proto, t2_ptr)),
            ) if *t1_proto == t2_proto => match (t1_ptr, t2_ptr) {
                (ir::Ty::Pointer(t1, true), ir::Ty::Pointer(t2, _)) if t1 == t2 => {
                    let item =
                        self.monomorphize_lang_item(LangItemKind::DynConstCoerce, [*t1_proto])?;

                    let func = self.exprs.function(item, rhs.span);
                    return self.call(func, [rhs].into_iter(), lhs_typ, rhs.span);
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
                ir::Ty::Pointer(t1, t1_const) if *t1 == *t2 && (!t2_const || *t1_const) => {
                    let size_lit = self.exprs.literal(
                        Value::USize(*size),
                        self.types.builtin(BuiltinType::USize),
                        rhs.span,
                    );
                    let item = self.monomorphize_lang_item(LangItemKind::SliceNew, [*t1_ptr])?;

                    let func = self.exprs.function(item, rhs.span);

                    let data = self.exprs.r#ref(
                        self.exprs
                            .const_index(self.exprs.deref(rhs, rhs.span), 0, rhs.span),
                        rhs.span,
                    );

                    return self.call(
                        func,
                        [data, size_lit],
                        item.get_function()
                            .map_err(|e| self.diag.err(e))?
                            .return_type,
                        rhs.span,
                    );
                }
                _ => {}
            },
            (Some(LangTypeKind::Dyn(t1_proto, t1_ptr)), ir::Ty::Pointer(t2, t2_const)) => {
                match t1_ptr {
                    ir::Ty::Pointer(_, t1_const) if !t2_const || *t1_const => {
                        let ty = self.types.pointer(t2, *t1_const);
                        let item =
                            self.monomorphize_lang_item(LangItemKind::DynNew, [*t1_proto, ty])?;
                        let func = self.exprs.function(item, rhs.span);
                        return self.call(
                            func,
                            [rhs],
                            item.get_function()
                                .map_err(|e| self.diag.err(e))?
                                .return_type,
                            rhs.span,
                        );
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        Err(mismatch!(self, lhs_typ, rhs.ty))
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
                .map(|typ| self.lower_type_unrestricted(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            return self.monomorphize_item(item, generic_args);
        }

        if fun.placeholders.is_empty() {
            return self.monomorphize_item(item, &[]);
        }

        // If the function is generic but no args are provided, we can try to infer the args
        // based on the types of the function's parameters and provided arguments in matching
        // positions and the return type with type_hint Since we have not yet monomorphized the
        // arguments, we do so tentatively in a fresh monomorphizer without the type_hint.
        // If the monomorphization of an argument fails for whatever reason, we skip that arg,
        // but do not rethrow the error as the resolution might still succeed.

        let mut infer_pairs = Vec::new();

        let self_slot = self_expr.map(|self_expr| (fun.args[0].typ, self_expr.ty));

        let mut tentative_errors = Vec::new();
        let self_count = self_expr.iter().count();

        if let Some(args) = tentative_args {
            if fun.args.len() != args.len() + self_count {
                return Err(self.diag.err(CodeErrorKind::ParamCountMismatch(
                    fun.args.len() - self_count,
                    args.len(),
                )));
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

            infer_pairs.extend(
                fun.args
                    .iter()
                    .skip(self_count)
                    .zip(args_hint.iter())
                    .map(|(p, e)| (p.typ, *e)),
            );
        }

        if let Some(return_type_hint) = return_type_hint {
            infer_pairs.push((fun.return_type, return_type_hint));
        }

        let mut type_inferer =
            TypeInferer::new(self.mono_ctx.ast, self.mono_ctx, fun.placeholders.to_vec());

        match type_inferer.try_infer(self_slot, infer_pairs) {
            Some(generic_args) => {
                self.monomorphize_item(item, generic_args.alloc_on(self.mono_ctx.ir))
            }
            None => Err(self.diag.err(CodeErrorKind::TypeInferenceFailed)),
        }
    }

    fn try_resolve_struct(
        &mut self,
        typ: ast::TyP<'ast>,
        initializers: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let (item, generic_args) = match typ {
            ast::Ty::Item(item) => (*item, None),
            ast::Ty::Generic(ast::Ty::Item(item), generic_args) => (*item, Some(*generic_args)),
            _ => {
                let lowered = self.lower_type_for_value(typ)?;
                match lowered {
                    ir::Ty::Item(item) if item.is_struct_like() => return Ok(item),
                    _ => return Err(self.diag.err(CodeErrorKind::StructLikeExpectedHere)),
                }
            }
        };

        let r#struct = match item.get() {
            ast::Item::StructLike(s) => s,
            _ => return Err(self.diag.err(CodeErrorKind::StructLikeExpectedHere)),
        };

        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type_unrestricted(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            return self.monomorphize_item(item, generic_args);
        }

        // If the struct is not generic, we don't need to infer the args
        if r#struct.placeholders.is_empty() {
            return self.monomorphize_item(item, &[]);
        }

        // If the parent of this expression expects a specific struct, we trust that this is
        // in fact the correct monomorphization.
        if let Some(ir::Ty::Item(hint_item)) = type_hint {
            let MonoKey(ast_hint_item, _, _, _) = self.mono_ctx.reverse_lookup(hint_item);
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
            self.mono_ctx.ast,
            self.mono_ctx,
            r#struct.placeholders.to_vec(),
        );
        let infer_result = type_inferer.try_infer(None, pairs);

        match infer_result {
            Some(generic_args) => {
                self.monomorphize_item(item, generic_args.alloc_on(self.mono_ctx.ir))
            }
            None => Err(self.diag.err(CodeErrorKind::TypeInferenceFailed)),
        }
    }

    /// Take reference of anything, promoting the lifetime if it is a rvalue.
    fn r#ref(&mut self, expr: ir::ExprP<'ir>, span: Option<Span>) -> ir::ExprP<'ir> {
        if matches!(expr.value_type, ValueType::LValue) {
            return self.exprs.r#ref(expr, span);
        }

        let id = self.mono_ctx.ir.make_id();
        self.local_defs.push(ir::LocalDef { id, typ: expr.ty });
        self.local_types.insert(id, expr.ty);

        let local = self.exprs.local(id, expr.ty, span);
        self.exprs.block(
            [ir::Statement::Expression(
                self.exprs.assign(local, expr, span),
            )],
            self.exprs.r#ref(local, span),
            span,
        )
    }

    fn autoref(
        &mut self,
        expr: ir::ExprP<'ir>,
        target: ir::TyP<'ir>,
        span: Option<Span>,
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
                    expr = self.r#ref(expr, span);
                }
                Ok(expr)
            }
            n if n > 0 => {
                let mut expr = expr;
                for _ in 0..n {
                    expr = self.exprs.deref(expr, span);
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

            // Equality comparison for enums
            (Item(l), Eq | Neq, Item(r))
                if l == r
                    && matches!(l.get().map_err(|e| self.diag.err(e))?, ir::IRItem::Enum(_)) =>
            {
                self.types.builtin(BuiltinType::Bool)
            }

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

            // Bit shifts
            (Builtin(l), LShift | RShift, Builtin(r)) if l.is_integer() && r.is_integer() => lhs.ty,

            // Pointer arithmetic
            (Pointer(l, l_const), Minus, Pointer(r, r_const)) if l == r && l_const == r_const => {
                self.types.builtin(BuiltinType::ISize)
            }
            (Pointer(_l, _), Plus | Minus, Builtin(BuiltinType::ISize | BuiltinType::USize)) => {
                lhs.ty
            }

            _ => {
                return Err(self.diag.err(CodeErrorKind::InvalidBinOp(
                    op,
                    self.mono_ctx.type_name(lhs.ty).unwrap(),
                    self.mono_ctx.type_name(rhs.ty).unwrap(),
                )))
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

                let must_use = match expr.ty {
                    ir::Ty::Item(item) => match item.get().map_err(|e| self.diag.err(e))? {
                        ir::IRItem::StructLike(s) => {
                            s.attributes.contains(&ast::Attribute::MustUse)
                        }
                        _ => false,
                    },
                    _ => false,
                };

                if must_use && !self.tentative {
                    let type_name = self.mono_ctx.type_name(expr.ty)?;
                    self.diag.warn(CodeErrorKind::UnusedMustUse(type_name))
                }

                Some(ir::Statement::Expression(expr))
            }
            ast::StatementKind::LetDeclaration(decl) => {
                let id = self.mono_ctx.map_id(decl.id);
                let type_hint = decl.typ.map(|t| self.lower_type_for_value(t)).transpose()?;
                let init = decl
                    .value
                    .map(|v| {
                        self.lower_expr(
                            v,
                            type_hint.or_else(|| self.local_type_hints.get(&id).copied()),
                        )
                    })
                    .transpose()?;

                match (type_hint, init) {
                    (None, None) => return Err(self.diag.err(CodeErrorKind::TypeHintRequired)),
                    (Some(ty), None) => {
                        self.local_types.insert(id, ty);
                        self.local_defs.push(ir::LocalDef { id, typ: ty });
                        None
                    }
                    (None, Some(init)) => {
                        self.local_types.insert(id, init.ty);
                        self.local_defs.push(ir::LocalDef { id, typ: init.ty });

                        if init.diverges() {
                            return Ok(Some(ir::Statement::Expression(init)));
                        }

                        Some(ir::Statement::Expression(self.exprs.assign(
                            self.exprs.local(id, init.ty, stmt.span),
                            init,
                            stmt.span,
                        )))
                    }
                    (Some(ty), Some(init)) => {
                        self.local_types.insert(id, ty);
                        self.local_defs.push(ir::LocalDef { id, typ: ty });

                        if init.diverges() {
                            return Ok(Some(ir::Statement::Expression(init)));
                        }

                        let init = self.try_coerce(ty, init)?;
                        Some(ir::Statement::Expression(self.exprs.assign(
                            self.exprs.local(id, ty, stmt.span),
                            init,
                            stmt.span,
                        )))
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
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let mut local_id: Option<ir::IrId> = None;
        if let ast::ExprKind::Local(id) = ret.kind {
            // This is a hack so the following works:
            // let a: Ty = { let b = a; ...; b };
            let id = self.mono_ctx.map_id(id);
            if let Some(ty) = type_hint {
                local_id = Some(id);
                self.local_type_hints.insert(id, ty);
            }
        }

        let ret = self.lower_block_inner(statements, ret, type_hint, ast_span);
        if let Some(id) = local_id {
            self.local_type_hints.remove(&id);
        }

        ret
    }

    fn lower_block_inner(
        &mut self,
        statements: &'ast [ast::Statement<'ast>],
        ret: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let (statements, errors): (Vec<_>, Vec<_>) = statements
            .iter()
            .map(|stmt| {
                let _guard = self.diag.push_span(stmt.span);
                self.lower_stmt(stmt)
            })
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

        Ok(self.exprs.block(
            statements.into_iter().flat_map(|e| e.unwrap()),
            ret,
            ast_span,
        ))
    }

    fn convert_int_literal(
        &mut self,
        sign: bool,
        value: u128,
        ty: ir::TyP<'ir>,
    ) -> Result<Value<'ir>, AluminaError> {
        let maybe_value = if sign {
            let as_i128 = if value == (i128::MAX as u128) + 1 {
                Ok(i128::MIN)
            } else {
                let v: Result<i128, _> = value.try_into();
                v.map(|v| -v)
            };

            as_i128.and_then(|v| match ty {
                ir::Ty::Builtin(BuiltinType::I8) => v.try_into().map(Value::I8).map(Some),
                ir::Ty::Builtin(BuiltinType::I16) => v.try_into().map(Value::I16).map(Some),
                ir::Ty::Builtin(BuiltinType::I32) => v.try_into().map(Value::I32).map(Some),
                ir::Ty::Builtin(BuiltinType::I64) => v.try_into().map(Value::I64).map(Some),
                ir::Ty::Builtin(BuiltinType::I128) => Ok(Some(Value::I128(v))),
                ir::Ty::Builtin(BuiltinType::ISize) => v.try_into().map(Value::ISize).map(Some),
                _ => Ok(None),
            })
        } else {
            let val = match ty {
                ir::Ty::Builtin(BuiltinType::U8) => value.try_into().map(Value::U8),
                ir::Ty::Builtin(BuiltinType::U16) => value.try_into().map(Value::U16),
                ir::Ty::Builtin(BuiltinType::U32) => value.try_into().map(Value::U32),
                ir::Ty::Builtin(BuiltinType::U64) => value.try_into().map(Value::U64),
                ir::Ty::Builtin(BuiltinType::U128) => Ok(Value::U128(value)),
                ir::Ty::Builtin(BuiltinType::USize) => value.try_into().map(Value::USize),
                ir::Ty::Builtin(BuiltinType::I8) => value.try_into().map(Value::I8),
                ir::Ty::Builtin(BuiltinType::I16) => value.try_into().map(Value::I16),
                ir::Ty::Builtin(BuiltinType::I32) => value.try_into().map(Value::I32),
                ir::Ty::Builtin(BuiltinType::I64) => value.try_into().map(Value::I64),
                ir::Ty::Builtin(BuiltinType::I128) => value.try_into().map(Value::I128),
                ir::Ty::Builtin(BuiltinType::ISize) => value.try_into().map(Value::ISize),
                _ => unreachable!(),
            };

            val.map(Some)
        };

        match maybe_value {
            Ok(Some(v)) => Ok(v),
            _ => {
                let value = format!("{}{}", if sign { "-" } else { "" }, value);
                let type_name = self.mono_ctx.type_name(ty)?;

                Err(self
                    .diag
                    .err(CodeErrorKind::IntegerOutOfRange(value, type_name)))
            }
        }
    }

    fn lower_lit(
        &mut self,
        ret: &ast::Lit<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let result = match ret {
            ast::Lit::Bool(v) => self.exprs.literal(
                Value::Bool(*v),
                self.types.builtin(BuiltinType::Bool),
                ast_span,
            ),
            ast::Lit::Null => {
                let ty = match type_hint {
                    Some(ir::Ty::Pointer(inner, is_const)) => self.types.pointer(inner, *is_const),
                    _ => self.types.pointer(self.types.void(), true),
                };

                self.exprs.literal(Value::USize(0), ty, ast_span)
            }
            ast::Lit::Int(sign, v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => self.types.builtin(*t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_integer() => self.types.builtin(*k),
                    _ => self.types.builtin(BuiltinType::I32),
                };

                let value = self.convert_int_literal(*sign, *v, ty)?;
                self.exprs.literal(value, ty, ast_span)
            }
            ast::Lit::Float(v, kind) => {
                let ty = match (kind, type_hint) {
                    (Some(t), _) => self.types.builtin(*t),
                    (None, Some(ir::Ty::Builtin(k))) if k.is_float() => self.types.builtin(*k),
                    _ => self.types.builtin(BuiltinType::F64),
                };

                let ir_str = v.alloc_on(self.mono_ctx.ir);

                match ty {
                    ir::Ty::Builtin(BuiltinType::F32) => {
                        self.exprs.literal(Value::F32(ir_str), ty, ast_span)
                    }
                    ir::Ty::Builtin(BuiltinType::F64) => {
                        self.exprs.literal(Value::F64(ir_str), ty, ast_span)
                    }
                    _ => ice!("unexpected type for the float literal"),
                }
            }
            ast::Lit::Str(v) => self.string_of(v, ast_span)?,
        };

        Ok(result)
    }

    fn lower_deref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner = self.lower_expr(inner, type_hint.map(|ty| self.types.pointer(ty, true)))?;
        if inner.diverges() {
            return Ok(inner);
        }

        let result = match inner.ty {
            ir::Ty::Pointer(_, _) => self.exprs.deref(inner, ast_span),
            _ => return Err(mismatch!(self, "pointer", inner.ty)),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_ref(
        &mut self,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
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

        Ok(self.r#ref(inner, ast_span))
    }

    fn lower_local(
        &mut self,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let id = self.mono_ctx.map_id(id);
        let typ = self
            .local_types
            .get(&id)
            .copied()
            .ok_or_else(|| self.diag.err(CodeErrorKind::LocalWithUnknownType))?;

        Ok(self.exprs.local(id, typ, ast_span))
    }

    fn lower_bound_param(
        &mut self,
        self_arg: ast::AstId,
        field_id: ast::AstId,
        bound_type: BoundItemType,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let self_arg = self.mono_ctx.map_id(self_arg);
        let field_id = self.mono_ctx.map_id(field_id);

        let typ = self
            .local_types
            .get(&self_arg)
            .copied()
            .ok_or_else(|| self.diag.err(CodeErrorKind::LocalWithUnknownType))?;

        match typ.canonical_type() {
            ir::Ty::Item(item) => {
                let closure = item.get_closure().map_err(|e| self.diag.err(e))?;
                let field_ty = closure
                    .data
                    .fields
                    .iter()
                    .find(|f| f.id == field_id)
                    .unwrap()
                    .ty;

                let mut obj = self.exprs.local(self_arg, typ, ast_span);
                while let ir::Ty::Pointer(_, _) = obj.ty {
                    obj = self.exprs.deref(obj, ast_span);
                }
                if let BoundItemType::ByValue = bound_type {
                    Ok(self.exprs.field(obj, field_id, field_ty, ast_span))
                } else {
                    Ok(self.exprs.deref(
                        self.exprs.field(obj, field_id, field_ty, ast_span),
                        ast_span,
                    ))
                }
            }
            _ => unreachable!(),
        }
    }

    fn lower_static(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&'ast [ast::TyP<'ast>]>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type_unrestricted(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            self.monomorphize_item(item, generic_args)?
        } else {
            self.monomorphize_item(item, &[])?
        };

        let item = item_cell.get_static().map_err(|e| self.diag.err(e))?;
        Ok(self.exprs.static_var(item_cell, item.typ, ast_span))
    }

    fn lower_const(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&'ast [ast::TyP<'ast>]>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|typ| self.lower_type_unrestricted(typ))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.mono_ctx.ir);

            self.monomorphize_item(item, generic_args)?
        } else {
            self.monomorphize_item(item, &[])?
        };
        let r#const = item_cell.get_const().map_err(|e| self.diag.err(e))?;
        Ok(self.exprs.const_var(item_cell, r#const.typ, ast_span))
    }

    fn lower_unary(
        &mut self,
        op: ast::UnOp,
        inner: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
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
                return Err(self.diag.err(CodeErrorKind::InvalidUnOp(
                    op,
                    self.mono_ctx.type_name(inner.ty).unwrap(),
                )));
            }
        };

        Ok(self.exprs.unary(op, inner, inner.ty, ast_span))
    }

    fn invoke_custom_binary(
        &mut self,
        op: ast::BinOp,
        lhs: ir::ExprP<'ir>,
        rhs: ir::ExprP<'ir>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item = self.monomorphize_lang_item(LangItemKind::Operator(op), [lhs.ty])?;
        let func = self.exprs.function(item, ast_span);

        let rhs = self.try_coerce(lhs.ty, rhs)?;

        let lhs = self.r#ref(lhs, ast_span);
        let rhs = self.r#ref(rhs, ast_span);

        self.call(
            func,
            [lhs, rhs].into_iter(),
            item.get_function()
                .map_err(|e| self.diag.err(e))?
                .return_type,
            ast_span,
        )
    }

    fn lower_binary(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::ExprP<'ast>,
        rhs: &ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
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
            return Ok(self.exprs.diverges([lhs, rhs], ast_span));
        }

        match self.typecheck_binary(op, lhs, rhs) {
            Ok(result_typ) => Ok(self.exprs.binary(op, lhs, rhs, result_typ, ast_span)),
            // Operator overloading
            Err(AluminaError::CodeErrors(errors1))
                if matches!(op, Eq | Neq | Lt | Gt | GEq | LEq) =>
            {
                match self.invoke_custom_binary(op, lhs, rhs, ast_span) {
                    Ok(expr) => Ok(expr),
                    Err(AluminaError::CodeErrors(errors2)) => Err(AluminaError::CodeErrors(
                        errors1.into_iter().chain(errors2).collect(),
                    )),
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    fn lower_assign_op(
        &mut self,
        op: ast::BinOp,
        lhs: &ast::ExprP<'ast>,
        rhs: &ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
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
            return Ok(self.exprs.diverges([lhs, rhs], ast_span));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(self.diag.err(CodeErrorKind::CannotAssignToRValue));
        }

        if lhs.is_const {
            return Err(self.diag.err(CodeErrorKind::CannotAssignToConst));
        }

        self.typecheck_binary(op, lhs, rhs)?;

        Ok(self.exprs.assign_op(op, lhs, rhs, ast_span))
    }

    fn lower_assign(
        &mut self,
        inner: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let lhs = self.lower_expr(inner, None)?;
        let rhs = self.lower_expr(rhs, Some(lhs.ty))?;

        if lhs.diverges() || rhs.diverges() {
            return Ok(self.exprs.diverges([lhs, rhs], ast_span));
        }

        if lhs.value_type != ir::ValueType::LValue {
            return Err(self.diag.err(CodeErrorKind::CannotAssignToRValue));
        }

        if lhs.is_const {
            return Err(self.diag.err(CodeErrorKind::CannotAssignToConst));
        }

        let rhs = self.try_coerce(lhs.ty, rhs)?;

        Ok(self.exprs.assign(lhs, rhs, ast_span))
    }

    fn lower_if(
        &mut self,
        cond_: ast::ExprP<'ast>,
        then: ast::ExprP<'ast>,
        els_: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let cond = self.lower_expr(cond_, Some(self.types.builtin(BuiltinType::Bool)))?;
        let mut then = self.lower_expr(then, type_hint)?;
        let mut els = self.lower_expr(els_, type_hint.or(Some(then.ty)))?;

        if cond.diverges() {
            return Ok(cond);
        }

        let cond = self.try_coerce(self.types.builtin(BuiltinType::Bool), cond)?;

        let gcd = ir::Ty::gcd(then.ty, els.ty);
        if !gcd.assignable_from(then.ty) || !gcd.assignable_from(els.ty) {
            if let Some(hint) = type_hint {
                // If the user supplied a type hint to the if expression, we can try coercing to it
                // this is mostly for &T and &U -> &dyn Proto coercion where T and U are distinct types
                // but satisfy the same protocol
                if let (Ok(a), Ok(b)) = (self.try_coerce(hint, then), self.try_coerce(hint, els)) {
                    then = a;
                    els = b;
                } else {
                    return Err(self.diag.err(CodeErrorKind::MismatchedBranchTypes(
                        self.mono_ctx.type_name(then.ty).unwrap(),
                        self.mono_ctx.type_name(els.ty).unwrap(),
                    )));
                }
            } else {
                return Err(self.diag.err(CodeErrorKind::MismatchedBranchTypes(
                    self.mono_ctx.type_name(then.ty).unwrap(),
                    self.mono_ctx.type_name(els.ty).unwrap(),
                )));
            }
        }

        Ok(self.exprs.if_then(cond, then, els, ast_span))
    }

    fn static_cond_matches(
        &mut self,
        cond: &ast::StaticIfCondition<'ast>,
    ) -> Result<bool, AluminaError> {
        let typ = self.lower_type_unrestricted(cond.typ)?;

        let mut found = false;
        for bound in cond.bounds.bounds {
            let _guard = self.diag.push_span(bound.span);

            let bound_typ = self.lower_type_unrestricted(bound.typ)?;
            match self.check_protocol_bound(bound_typ, typ)? {
                BoundCheckResult::Matches if bound.negated => {
                    if cond.bounds.kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    return Ok(false);
                }
                BoundCheckResult::DoesNotMatch | BoundCheckResult::DoesNotMatchBecause(_)
                    if !bound.negated =>
                {
                    if cond.bounds.kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    return Ok(false);
                }
                _ => {
                    found = true;
                    if cond.bounds.kind == ast::ProtocolBoundsKind::Any {
                        break;
                    }
                }
            }
        }
        Ok(found)
    }

    fn lower_static_if(
        &mut self,
        cond: &ast::StaticIfCondition<'ast>,
        then: ast::ExprP<'ast>,
        els: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        _ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.static_cond_matches(cond)? {
            self.lower_expr(then, type_hint)
        } else {
            self.lower_expr(els, type_hint)
        }
    }

    fn lower_tuple(
        &mut self,
        exprs: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
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
            return Ok(self.exprs.diverges(lowered, ast_span));
        }

        let element_types: Vec<_> = lowered.iter().map(|e| e.ty).collect();
        let tuple_type = self.types.tuple(element_types);

        Ok(self
            .exprs
            .tuple(lowered.into_iter().enumerate(), tuple_type, ast_span)
            .alloc_on(self.mono_ctx.ir))
    }

    fn lower_cast(
        &mut self,
        expr: ast::ExprP<'ast>,
        target_type: ast::TyP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let expr = self.lower_expr(expr, None)?;
        if expr.diverges() {
            return Ok(expr);
        }

        let typ = self.lower_type_for_value(target_type)?;

        // If the type coerces automatically, no cast is required
        if let Ok(expr) = self.try_coerce(typ, expr) {
            return Ok(self.exprs.coerce(expr, typ, ast_span));
        }

        let ty_lang = self.mono_ctx.get_lang_type_kind(typ);
        let expr_lang = self.mono_ctx.get_lang_type_kind(expr.ty);

        // (Dangerous) Const to mut casts for lang objects
        match (ty_lang, expr_lang) {
            // &[T] -> &mut [T]
            (
                Some(LangTypeKind::Slice(ir::Ty::Pointer(t1, _))),
                Some(LangTypeKind::Slice(ir::Ty::Pointer(t2, _))),
            ) if *t1 == *t2 => {
                let item = self.monomorphize_lang_item(LangItemKind::SliceConstCast, [*t1])?;

                let func = self.exprs.function(item, ast_span);
                return self.call(
                    func,
                    [expr].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                );
            }
            // &dyn Proto -> &mut dyn Proto
            (Some(LangTypeKind::Dyn(t1_proto, _)), Some(LangTypeKind::Dyn(t2_proto, _)))
                if *t1_proto == *t2_proto =>
            {
                let item = self.monomorphize_lang_item(LangItemKind::DynConstCast, [t1_proto])?;

                let func = self.exprs.function(item, ast_span);
                return self.call(
                    func,
                    [expr].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                );
            }

            // &dyn Proto -> any pointer (unchecked downcast)
            (_, Some(LangTypeKind::Dyn(t2_proto, t2_const)))
                if matches!(typ, ir::Ty::Pointer(_, _)) =>
            {
                let item =
                    self.monomorphize_lang_item(LangItemKind::DynData, [t2_proto, t2_const])?;
                let func = self.exprs.function(item, ast_span);
                let call = self.call(
                    func,
                    [expr].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                )?;
                return Ok(self.exprs.cast(call, typ, ast_span));
            }
            _ => {}
        }

        match (expr.ty, typ) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            // bool -> integer (but not vice-versa)
            (ir::Ty::Builtin(BuiltinType::Bool), ir::Ty::Builtin(b)) if b.is_numeric() => {}

            // Enums
            (ir::Ty::Item(a), ir::Ty::Builtin(b))
                if matches!(a.get().map_err(|e| self.diag.err(e))?, ir::IRItem::Enum(_))
                    && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Item(b))
                if matches!(b.get().map_err(|e| self.diag.err(e))?, ir::IRItem::Enum(_))
                    && a.is_numeric() => {}

            // Pointer casts
            (
                ir::Ty::Pointer(_, _) | ir::Ty::FunctionPointer(_, _),
                ir::Ty::Pointer(_, _) | ir::Ty::FunctionPointer(_, _),
            ) => {
                // Yes, even const -> mut casts, if you do this you are on your own
            }
            (
                ir::Ty::Builtin(BuiltinType::USize),
                ir::Ty::Pointer(_, _) | ir::Ty::FunctionPointer(_, _),
            ) => {}
            (
                ir::Ty::Pointer(_, _) | ir::Ty::FunctionPointer(_, _),
                ir::Ty::Builtin(BuiltinType::USize),
            ) => {}

            _ => {
                return Err(self.diag.err(CodeErrorKind::InvalidCast(
                    self.mono_ctx.type_name(expr.ty).unwrap(),
                    self.mono_ctx.type_name(typ).unwrap(),
                )))
            }
        }

        Ok(self.exprs.cast(expr, typ, ast_span))
    }

    fn lower_loop(
        &mut self,
        body: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
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
            ir::Statement::Expression(self.exprs.goto(continue_label, ast_span)),
            ir::Statement::Label(break_label),
        ];

        let result = match self.local_types.get(&loop_result) {
            None => self
                .exprs
                .block(statements, self.exprs.unreachable(ast_span), ast_span),
            Some(typ) => {
                self.local_defs.push(ir::LocalDef {
                    id: loop_result,
                    typ,
                });
                self.exprs.block(
                    statements,
                    self.exprs.local(loop_result, typ, ast_span),
                    ast_span,
                )
            }
        };

        Ok(result)
    }

    fn lower_break(
        &mut self,
        expr: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self
            .loop_contexts
            .last()
            .cloned()
            .ok_or_else(|| self.diag.err(CodeErrorKind::BreakOutsideOfLoop))?;

        let expr = expr
            .map(|e| self.lower_expr(e, loop_context.type_hint))
            .transpose()?;

        if expr.map(|e| e.diverges()).unwrap_or(false) {
            return Ok(expr.unwrap());
        }

        let break_typ = expr.map(|e| e.ty).unwrap_or_else(|| self.types.void());

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
            .unwrap_or_else(|| {
                self.exprs
                    .void(self.types.void(), ir::ValueType::RValue, ast_span)
            });

        let statements = [ir::Statement::Expression(
            self.exprs.assign(
                self.exprs
                    .local(loop_context.loop_result, slot_type, ast_span),
                expr,
                ast_span,
            ),
        )];

        Ok(self.exprs.block(
            statements,
            self.exprs.goto(loop_context.break_label, ast_span),
            ast_span,
        ))
    }

    fn lower_continue(
        &mut self,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_context = self
            .loop_contexts
            .last()
            .cloned()
            .ok_or_else(|| self.diag.err(CodeErrorKind::ContinueOutsideOfLoop))?;

        Ok(self.exprs.goto(loop_context.continue_label, ast_span))
    }

    fn lower_intrinsic(
        &mut self,
        span: Option<ast::Span>,
        callee: &ast::Intrinsic,
        generic_args: &[ast::TyP<'ast>],
        args: &[ast::ExprP<'ast>],
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if callee.generic_count != generic_args.len() {
            return Err(self.diag.err(CodeErrorKind::GenericParamCountMismatch(
                callee.generic_count,
                generic_args.len(),
            )));
        }

        if (callee.arg_count != args.len()) && !(callee.varargs && args.len() >= callee.arg_count) {
            return Err(self.diag.err(CodeErrorKind::ParamCountMismatch(
                callee.arg_count,
                args.len(),
            )));
        }

        let generic_args = generic_args
            .iter()
            .map(|e| self.lower_type_unrestricted(e))
            .collect::<Result<Vec<_>, _>>()?;

        let args = args
            .iter()
            .map(|e| self.lower_expr(e, None))
            .collect::<Result<Vec<_>, _>>()?;

        match callee.kind {
            IntrinsicKind::TestCases => self.generate_test_cases(),
            IntrinsicKind::MakeVtable => {
                if let ir::Ty::Tuple(inner) = generic_args[0] {
                    self.generate_vtable(inner, generic_args[1])
                } else {
                    ice!("creating a vtable with something that's not a tuple of protocols")
                }
            }
            IntrinsicKind::EnumVariants => self.generate_enum_variants(generic_args[0]),
            IntrinsicKind::TypeName => {
                let typ = generic_args[0];
                let name = self.mono_ctx.type_name(typ)?;

                Ok(self.string_of(name.as_bytes(), span)?)
            }
            IntrinsicKind::SizeOf => self.size_of(generic_args[0], span),
            IntrinsicKind::AlignOf => self.align_of(generic_args[0], span),
            IntrinsicKind::TypeId => self.type_id(generic_args[0], span),
            IntrinsicKind::ArrayLengthOf => self.array_length_of(generic_args[0], span),
            IntrinsicKind::Trap => self.trap(span),
            IntrinsicKind::CompileFail => self.compile_fail(args[0], span),
            IntrinsicKind::CompileWarn => self.compile_warn(args[0], span),
            IntrinsicKind::CompileNote => self.compile_note(args[0], span),
            IntrinsicKind::Unreachable => self.unreachable(span),
            IntrinsicKind::Asm => self.asm(args[0], span),
            IntrinsicKind::CodegenFunc => {
                self.codegen_func(args[0], &args[1..], generic_args[0], span)
            }
            IntrinsicKind::CodegenConst => self.codegen_const(args[0], generic_args[0], span),
            IntrinsicKind::CodegenTypeFunc => {
                self.codegen_type_func(args[0], generic_args[0], generic_args[1], span)
            }
            IntrinsicKind::Uninitialized => self.uninitialized(generic_args[0], span),
            IntrinsicKind::Dangling => self.dangling(generic_args[0], span),
            IntrinsicKind::InConstContext => self.in_const_context(span),
        }
    }

    fn array_of<I>(
        &mut self,
        element_type: ir::TyP<'ir>,
        elems: I,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError>
    where
        I: IntoIterator<Item = ir::ExprP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = elems.into_iter();
        let array_type = self.types.array(element_type, iter.len());

        Ok(self.exprs.array(iter, array_type, span))
    }

    fn string_of(
        &mut self,
        value: &[u8],
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let ptr_type = self
            .types
            .pointer(self.types.builtin(BuiltinType::U8), true);

        let make_slice = self.monomorphize_lang_item(LangItemKind::SliceNew, [ptr_type])?;

        let data = self.exprs.literal(
            Value::Str(self.mono_ctx.ir.arena.alloc_slice_copy(value), 0),
            ptr_type,
            span,
        );
        let size = self.exprs.literal(
            Value::USize(value.len()),
            self.types.builtin(BuiltinType::USize),
            span,
        );

        self.call(
            self.exprs.function(make_slice, span),
            [data, size],
            make_slice
                .get_function()
                .map_err(|e| self.diag.err(e))?
                .return_type,
            span,
        )
    }

    fn generate_test_cases(&mut self) -> Result<ir::ExprP<'ir>, AluminaError> {
        let tests = self.mono_ctx.tests.clone();

        let meta_item = self.monomorphize_lang_item(LangItemKind::TestCaseMeta, [])?;
        let meta_type = self.types.named(meta_item);
        let meta_new = self.monomorphize_lang_item(LangItemKind::TestCaseMetaNew, [])?;

        let fn_ptr_type = self.types.function([], self.types.void());

        let mut test_cases = vec![];
        for (func, meta) in tests.iter() {
            let name = meta.name.to_string();
            let path = meta.path.to_string();
            let attrs: Vec<_> = meta
                .attributes
                .iter()
                .map(|s| s.as_bytes())
                .collect::<Vec<_>>()
                .join(&b"\0"[..]);

            let fn_ptr_arg = self.exprs.function(func, None);
            let args = [
                self.string_of(path.as_bytes(), None)?,
                self.string_of(name.as_bytes(), None)?,
                self.string_of(&attrs, None)?,
                self.try_coerce(fn_ptr_type, fn_ptr_arg)?,
            ];

            test_cases.push(self.call(
                self.exprs.function(meta_new, None),
                args,
                meta_type,
                None,
            )?);
        }

        self.array_of(meta_type, test_cases, None)
    }

    pub fn call<I>(
        &mut self,
        callee: ir::ExprP<'ir>,
        args: I,
        return_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError>
    where
        I: IntoIterator<Item = ir::ExprP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        match callee.kind {
            ir::ExprKind::Fn(item) => {
                let func = item.get_function().map_err(|e| self.diag.err(e))?;
                if func.attributes.contains(&ast::Attribute::InlineDuringMono) {
                    // no silent fallback to a regular function call, since the only thing that can go wrong is that
                    // the callee is not compatible with IR inlining, so this should not lead to surprises
                    let (expr, mut additional_defs) = IrInliner::inline(
                        self.mono_ctx.ir,
                        func.body
                            .get()
                            .ok_or_else(|| self.diag.err(CodeErrorKind::UnpopulatedSymbol))?
                            .raw_body
                            .unwrap(),
                        func.args
                            .iter()
                            .zip(args.into_iter())
                            .map(|(a, b)| (a.id, b)),
                        span,
                    )?;

                    self.local_defs.append(&mut additional_defs);

                    // The inlined function may return a lvalue, which would be very confusing. If this happens, we
                    // patch up the value kind. C will still consider it a lvalue, but that shouldn't matter.
                    if expr.value_type == ir::ValueType::LValue {
                        return Ok(ir::Expr::rvalue(expr.kind.clone(), expr.ty, span)
                            .alloc_on(self.mono_ctx.ir));
                    } else {
                        return Ok(expr);
                    }
                }
            }
            _ => {}
        }
        Ok(self.exprs.call(callee, args, return_ty, span))
    }

    fn generate_enum_variants(
        &mut self,
        typ: ir::TyP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let e = match typ {
            ir::Ty::Item(item) => item.get_enum().map_err(|e| self.diag.err(e))?,
            _ => ice!("enum expected"),
        };

        let enum_variant_new = self.monomorphize_lang_item(LangItemKind::EnumVariantNew, [typ])?;
        let enum_variant_new_func = enum_variant_new
            .get_function()
            .map_err(|e| self.diag.err(e))?;

        let mut exprs = Vec::new();
        for member in e.members {
            let name = self.string_of(member.name.as_bytes(), None)?;
            let value = self.exprs.cast(member.value, typ, None);

            exprs.push(self.call(
                self.exprs.function(enum_variant_new, None),
                [name, value].into_iter(),
                enum_variant_new_func.return_type,
                None,
            )?);
        }

        self.array_of(enum_variant_new_func.return_type, exprs, None)
    }

    fn generate_vtable(
        &mut self,
        protocol_types: &'ir [ir::TyP<'ir>],
        concrete_type: ir::TyP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        for protocol_type in protocol_types.iter() {
            let protocol = match protocol_type {
                ir::Ty::Item(protocol) => protocol,
                _ => ice!("protocol expected"),
            };
            let proto_key = self.mono_ctx.reverse_lookup(protocol);
            // Replace the dyn_self placeholder
            let args = std::iter::once(concrete_type)
                .chain(proto_key.1[1..].iter().copied())
                .collect::<Vec<_>>()
                .alloc_on(self.mono_ctx.ir);
            let actual_protocol = self.monomorphize_item(proto_key.0, args)?;
            let actual_protocol_type = self.types.named(actual_protocol);

            // We only rely on standard protocol bound matching to see if the vtable is compatible
            self.check_protocol_bounds(
                ast::ProtocolBoundsKind::All,
                concrete_type,
                vec![(None, actual_protocol_type, false)],
            )?;
        }

        let vtable_layout = self
            .mono_ctx
            .vtable_layouts
            .get(protocol_types)
            .ok_or_else(|| {
                self.diag.err(CodeErrorKind::InternalError(
                    "vtable layout not found".to_string(),
                    Backtrace::new().into(),
                ))
            })?
            .methods;

        let associated_fns = self.get_associated_fns(concrete_type)?;
        let mut attrs = Vec::new();

        for func in vtable_layout {
            // If the function is not found, that can only mean that someone is trying to convert a `dyn` into another
            // dyn. If it were not so, the compiler would have errored earlier (when checking the protocol bounds).
            // We'd need to generate a thunk for it and it's not worth the hassle.
            let function = associated_fns
                .get(&func.name)
                .ok_or_else(|| self.diag.err(CodeErrorKind::IndirectDyn))?;

            let candidate_fun = function.get_function();

            let mut type_inferer = TypeInferer::new(
                self.mono_ctx.ast,
                self.mono_ctx,
                candidate_fun.placeholders.to_vec(),
            );

            let infer_slots = candidate_fun
                .args
                .iter()
                .zip(
                    once(self.types.pointer(
                        concrete_type,
                        func.arg_types[0] == self.types.pointer(self.types.void(), true),
                    ))
                    .chain(func.arg_types.iter().skip(1).copied()),
                )
                .map(|(p, t)| (p.typ, t))
                .chain(once((candidate_fun.return_type, func.return_type)));

            let monomorphized = match type_inferer.try_infer(None, infer_slots) {
                Some(placeholders) => {
                    self.monomorphize_item(function, placeholders.alloc_on(self.mono_ctx.ir))?
                }
                _ => ice!("cannot infer types while generating vtable"),
            };

            attrs.push(self.exprs.cast(
                self.exprs.function(monomorphized, None),
                self.types.function([], self.types.void()),
                None,
            ));
        }

        let ret = self.array_of(self.types.function([], self.types.void()), attrs, None)?;

        Ok(ret)
    }

    fn lower_virtual_call(
        &mut self,
        protocol_types: &'ir [ir::TyP<'ir>],
        dyn_ptr: ir::TyP<'ir>,
        self_arg: ir::ExprP<'ir>,
        name: &'ast str,
        args: &[ast::ExprP<'ast>],
        ast_span: Option<Span>,
    ) -> Result<Option<ir::ExprP<'ir>>, AluminaError> {
        let layout = self
            .mono_ctx
            .vtable_layouts
            .get(protocol_types)
            .ok_or_else(|| {
                self.diag.err(CodeErrorKind::InternalError(
                    "vtable layout not found".to_string(),
                    Backtrace::new().into(),
                ))
            })?;

        let (vtable_index, func) = if let Some(x) = layout
            .methods
            .iter()
            .enumerate()
            .find(|(_, p)| p.name == name)
        {
            x
        } else {
            return Ok(None);
        };

        if func.arg_types.len() != args.len() + 1 {
            return Err(self.diag.err(CodeErrorKind::ParamCountMismatch(
                func.arg_types.len() - 1,
                args.len(),
            )));
        }

        // We need to store the dyn object in a temporary as it may have been produced by
        // an expression with side effects.
        let key = self.mono_ctx.ir.intern_type(ir::Ty::Tuple(protocol_types));

        let canonical = self_arg.ty.canonical_type();
        let temporary = self.mono_ctx.ir.make_id();
        let local = self.exprs.local(temporary, canonical, ast_span);
        self.local_defs.push(ir::LocalDef {
            id: temporary,
            typ: canonical,
        });
        let tgt = self.autoref(self_arg, canonical, ast_span)?;
        let data_item = self.monomorphize_lang_item(LangItemKind::DynData, [key, dyn_ptr])?;
        let index_item =
            self.monomorphize_lang_item(LangItemKind::DynVtableIndex, [key, dyn_ptr])?;
        let call = self.call(
            self.exprs.function(index_item, ast_span),
            [
                local,
                self.exprs.literal(
                    Value::USize(vtable_index),
                    self.types.builtin(BuiltinType::USize),
                    ast_span,
                ),
            ],
            index_item
                .get_function()
                .map_err(|e| self.diag.err(e))?
                .return_type,
            ast_span,
        )?;
        let callee = self.exprs.cast(
            call,
            self.types
                .function(func.arg_types.to_vec(), func.return_type),
            ast_span,
        );

        // A separate check for constness match for the self argument. It's not
        // required, as the one below will catch it, but we want to show a nicer
        // error message.
        if let (ir::Ty::Pointer(_, t1_const), ir::Ty::Pointer(_, t2_const)) =
            (dyn_ptr, func.arg_types[0])
        {
            if !*t2_const && *t1_const {
                let mut_dyn = self
                    .monomorphize_lang_item(LangItemKind::DynConstCast, [key])?
                    .get_function()
                    .map_err(|e| self.diag.err(e))?
                    .return_type;

                return Err(mismatch!(self, mut_dyn, self_arg.ty));
            }
        }

        let mut args = once(Ok(self.call(
            self.exprs.function(data_item, ast_span),
            [local],
            data_item
                .get_function()
                .map_err(|e| self.diag.err(e))?
                .return_type,
            ast_span,
        )?))
        .chain(
            args.iter()
                .zip(func.arg_types.iter().skip(1))
                .map(|(arg, ty)| self.lower_expr(arg, Some(ty))),
        )
        .collect::<Result<Vec<_>, _>>()?;

        if args.iter().any(|e| e.diverges()) {
            return Ok(Some(self.exprs.diverges(args, ast_span)));
        }

        for (expected, arg) in func.arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, arg)?;
        }

        let call = self.call(callee, args, func.return_type, ast_span)?;
        let ret = self.exprs.block(
            [ir::Statement::Expression(
                self.exprs.assign(local, tgt, ast_span),
            )],
            call,
            ast_span,
        );

        Ok(Some(ret))
    }

    fn lower_method_call(
        &mut self,
        self_arg: ast::ExprP<'ast>,
        unified_fn: Option<ast::ItemP<'ast>>,
        name: &'ast str,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<Option<ir::ExprP<'ir>>, AluminaError> {
        let ir_self_arg = self.lower_expr(self_arg, None)?;

        // Special case for struct fields (they have precedence over methods in .name resolution)
        if let ir::Ty::Item(item) = ir_self_arg.ty.canonical_type() {
            if let ir::IRItem::StructLike(_) = item.get().map_err(|e| self.diag.err(e))? {
                let fields = self.get_struct_field_map(item)?;
                if fields.contains_key(name) {
                    // This is not a method, but a field (e.g. a function pointer), go back to lower_call
                    // and process it as usual.
                    return Ok(None);
                }
            }
        };

        let canonical = ir_self_arg.ty.canonical_type();

        if let Some(LangTypeKind::Dyn(ir::Ty::Tuple(protocols), dyn_ptr)) =
            self.mono_ctx.get_lang_type_kind(canonical)
        {
            if let Some(result) =
                self.lower_virtual_call(protocols, dyn_ptr, ir_self_arg, name, args, ast_span)?
            {
                return Ok(Some(result));
            }
        }

        let method = self
            .get_associated_fns(canonical)?
            .get(name)
            .copied()
            .or(unified_fn)
            .ok_or_else(|| {
                self.diag.err(CodeErrorKind::MethodNotFound(
                    name.into(),
                    self.mono_ctx.type_name(canonical).unwrap(),
                ))
            })?;

        let method = self.try_resolve_function(
            method,
            None,
            Some(ir_self_arg),
            Some(args),
            type_hint,
            None,
        )?;

        let callee = self.exprs.function(method, ast_span);

        let fn_arg_types: Vec<_>;
        let (arg_types, return_type) = match callee.ty {
            ir::Ty::FunctionPointer(arg_types, return_type) => (*arg_types, *return_type),
            ir::Ty::Item(item) => {
                let fun = item.get_function().map_err(|e| self.diag.err(e))?;
                fn_arg_types = fun.args.iter().map(|p| p.ty).collect();
                (&fn_arg_types[..], fun.return_type)
            }
            _ => unreachable!(),
        };

        if arg_types.is_empty() {
            return Err(self.diag.err(CodeErrorKind::NotAMethod));
        }

        if arg_types.len() != args.len() + 1 {
            return Err(self.diag.err(CodeErrorKind::ParamCountMismatch(
                arg_types.len() - 1,
                args.len(),
            )));
        }

        let ir_self_arg = self.autoref(ir_self_arg, arg_types[0], self_arg.span)?;
        let mut args = once(Ok(ir_self_arg))
            .chain(
                args.iter()
                    .zip(arg_types.iter().skip(1))
                    .map(|(arg, ty)| self.lower_expr(arg, Some(ty))),
            )
            .collect::<Result<Vec<_>, _>>()?;

        if args.iter().any(|e| e.diverges()) {
            return Ok(Some(self.exprs.diverges(args, ast_span)));
        }

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, arg)?;
        }

        Ok(Some(self.call(callee, args, return_type, ast_span)?))
    }

    fn resolve_ast_type(
        &mut self,
        ast_type: ast::TyP<'ast>,
    ) -> Result<ast::TyP<'ast>, AluminaError> {
        let typ = match ast_type {
            ast::Ty::Generic(ast::Ty::Item(n), _) | ast::Ty::Item(n) => {
                if let ast::Item::TypeDef(ast::TypeDef {
                    target: Some(target),
                    ..
                }) = n.get()
                {
                    let _guard = self
                        .mono_ctx
                        .cycle_guardian
                        .guard((n, &[]))
                        .map_err(|_| self.diag.err(CodeErrorKind::CycleDetected))?;

                    return self.resolve_ast_type(target);
                }

                ast_type
            }
            ast::Ty::Placeholder(_) => {
                let ir_type = self.lower_type_for_value(ast_type)?;
                self.raise_type(ir_type)?
            }
            _ => ast_type,
        };

        Ok(typ)
    }

    fn resolve_defered_func(
        &mut self,
        spec: &ast::Defered<'ast>,
    ) -> Result<ast::ItemP<'ast>, AluminaError> {
        let typ = self.resolve_ast_type(spec.typ)?;
        let associated_fns = self.get_associated_fns_for_ast(typ)?;
        let func = associated_fns.get(spec.name).ok_or_else(|| {
            self.diag
                .err(CodeErrorKind::UnresolvedItem(spec.name.to_string()))
        })?;

        Ok(func)
    }

    fn lower_call(
        &mut self,
        callee: ast::ExprP<'ast>,
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // Unlike other AST nodes, calls are handled a bit specially, where we switch on the type of the
        // callee node before lowering it. This is because free-standing function-like values are treated
        // as function pointers, but we are also able to call things that cannot be turned into a function
        // pointer, such as methods, UFCS free functions and compiler intrinsics.
        let ast_callee = callee;
        let callee = match &callee.kind {
            ast::ExprKind::Fn(ast::FnKind::Normal(item), generic_args) => {
                if let ast::Item::Intrinsic(intrinsic) = item.get() {
                    return self.lower_intrinsic(
                        ast_callee.span,
                        intrinsic,
                        generic_args.unwrap_or(&[]),
                        args,
                    );
                }

                let item = self.try_resolve_function(
                    item,
                    *generic_args,
                    None,
                    Some(args),
                    type_hint,
                    None,
                )?;

                self.exprs.function(item, callee.span)
            }
            ast::ExprKind::Defered(spec) => {
                let func = self.resolve_defered_func(spec)?;
                let item =
                    self.try_resolve_function(func, None, None, Some(args), type_hint, None)?;

                self.exprs.function(item, callee.span)
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

                self.exprs.function(item, callee.span)
            }
            ast::ExprKind::Field(e, field, unified_fn) => {
                // Methods are resolved in the following order - field has precedence, then associated
                // functions, then free functions with UFCS. We never want UFCS to shadow native fields
                // and methods.
                match self.lower_method_call(e, *unified_fn, field, args, type_hint, ast_span)? {
                    Some(result) => return Ok(result),
                    None => self.lower_expr(callee, None)?,
                }
            }
            _ => self.lower_expr(callee, None)?,
        };

        let mut varargs = false;
        let mut self_arg = None;

        let fn_arg_types: Vec<_>;
        let (arg_types, return_type, callee) = match callee.ty {
            ir::Ty::FunctionPointer(arg_types, return_type) => (*arg_types, *return_type, callee),
            ir::Ty::Item(item) => match item.get().map_err(|e| self.diag.err(e))? {
                ir::IRItem::Closure(closure) => {
                    self_arg = Some(self.r#ref(callee, callee.span));

                    let fun_item = closure.function.get().unwrap();
                    let fun = fun_item.get_function().map_err(|e| self.diag.err(e))?;
                    fn_arg_types = fun.args.iter().skip(1).map(|p| p.ty).collect();

                    (
                        &fn_arg_types[..],
                        fun.return_type,
                        self.exprs.function(fun_item, callee.span),
                    )
                }
                ir::IRItem::Function(fun) => {
                    if fun.varargs {
                        varargs = true;
                    }
                    fn_arg_types = fun.args.iter().map(|p| p.ty).collect();

                    (&fn_arg_types[..], fun.return_type, callee)
                }
                _ => {
                    return Err(self.diag.err(CodeErrorKind::FunctionOrStaticExpectedHere));
                }
            },
            _ => {
                return Err(self.diag.err(CodeErrorKind::FunctionOrStaticExpectedHere));
            }
        };

        if !varargs && (arg_types.len() != args.len()) {
            return Err(self.diag.err(CodeErrorKind::ParamCountMismatch(
                arg_types.len(),
                args.len(),
            )));
        }

        if varargs && (arg_types.len() > args.len()) {
            return Err(self.diag.err(CodeErrorKind::ParamCountMismatch(
                arg_types.len(),
                args.len(),
            )));
        }

        let mut args = args
            .iter()
            .zip(
                // Pad with None for varargs
                arg_types
                    .iter()
                    .map(|t| Some(*t))
                    .chain(std::iter::repeat(None)),
            )
            .map(|(arg, ty)| self.lower_expr(arg, ty))
            .collect::<Result<Vec<_>, _>>()?;

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, arg)?;
        }

        if callee.diverges() || args.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(once(callee).chain(args), ast_span));
        }

        if let Some(self_arg) = self_arg {
            args.insert(0, self_arg);
        }

        self.call(callee, args, return_type, ast_span)
    }

    fn lower_fn(
        &mut self,
        kind: ast::FnKind<'ast>,
        generic_args: Option<&'ast [ast::TyP<'ast>]>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // TODO: Forward the type hint inside the function body.

        let fn_arg_types: Vec<_>;
        let (args_hint, return_type_hint) = match type_hint {
            Some(ir::Ty::FunctionPointer(arg_types, return_type)) => {
                (Some(*arg_types), Some(*return_type))
            }
            Some(ir::Ty::Item(item))
                if matches!(
                    item.get().map_err(|e| self.diag.err(e))?,
                    ir::IRItem::Function(_)
                ) =>
            {
                let fun = item.get_function().map_err(|e| self.diag.err(e))?;
                fn_arg_types = fun.args.iter().map(|p| p.ty).collect();
                (Some(&fn_arg_types[..]), Some(fun.return_type))
            }
            _ => (None, None),
        };

        let result = match kind {
            ast::FnKind::Normal(item) => {
                if let ast::Item::Intrinsic(_) = item.get() {
                    return Err(self.diag.err(CodeErrorKind::IntrinsicsAreSpecialMkay));
                }

                let item = self.try_resolve_function(
                    item,
                    generic_args,
                    None,
                    None,
                    return_type_hint,
                    args_hint,
                )?;

                self.exprs.function(item, ast_span)
            }
            ast::FnKind::Closure(bindings, func_item) => {
                let bound_values = bindings
                    .iter()
                    .map(|binding| {
                        let val = self.lower_expr(binding.value, None)?;
                        if let BoundItemType::ByValue = binding.binding_type {
                            Ok::<_, AluminaError>(val)
                        } else {
                            Ok(self.r#ref(val, binding.span))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let fields = bindings
                    .iter()
                    .zip(bound_values.iter())
                    .map(|(binding, expr)| {
                        Ok(ir::Field {
                            id: self.mono_ctx.map_id(binding.id),
                            ty: expr.ty,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                let key = self.get_mono_key(func_item, &[], false)?;
                let closure_typ = match self.mono_ctx.finished.entry(key.clone()) {
                    // The cell may be empty at this point if we are dealing with recursive references
                    // In this case, we will just return the item as is, but it will not
                    // be populated until the top-level item is finished.
                    Entry::Occupied(entry) => self.types.named(entry.get()),
                    Entry::Vacant(entry) => {
                        let closure = self.mono_ctx.ir.make_symbol();
                        self.mono_ctx.reverse_map.insert(closure, key.clone());
                        entry.insert(closure);

                        closure.assign(ir::IRItem::Closure(ir::Closure {
                            data: ir::StructLike {
                                name: None,
                                attributes: &[],
                                fields: fields.clone().alloc_on(self.mono_ctx.ir),
                                is_union: false,
                            },
                            function: OnceCell::new(),
                        }));

                        let closure_typ = self.types.named(closure);
                        let item = self.try_resolve_function(
                            func_item,
                            generic_args,
                            Some(self.exprs.local(
                                self.mono_ctx.ir.make_id(),
                                closure_typ,
                                ast_span,
                            )),
                            None,
                            return_type_hint,
                            args_hint,
                        )?;

                        closure
                            .get_closure()
                            .map_err(|e| self.diag.err(e))?
                            .function
                            .set(item)
                            .unwrap();

                        closure_typ
                    }
                };

                self.exprs.r#struct(
                    fields
                        .into_iter()
                        .zip(bound_values.into_iter())
                        .map(|(f, e)| (f.id, e)),
                    closure_typ,
                    ast_span,
                )
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

                self.exprs.function(item, ast_span)
            }
        };

        Ok(result)
    }

    fn lower_tuple_index(
        &mut self,
        tup: ast::ExprP<'ast>,
        index: usize,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let tup = self.lower_expr(tup, None)?;
        let result = match tup.ty.canonical_type() {
            ir::Ty::Tuple(types) => {
                if types.len() <= index {
                    return Err(self.diag.err(CodeErrorKind::TupleIndexOutOfBounds));
                }

                let mut tup = tup;
                while let ir::Ty::Pointer(_, _) = tup.ty {
                    tup = self.exprs.deref(tup, ast_span);
                }

                self.exprs.tuple_index(tup, index, types[index], ast_span)
            }
            _ => return Err(mismatch!(self, "tuple", tup.ty)),
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
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let obj = self.lower_expr(obj, None)?;

        let result = match obj.ty.canonical_type() {
            ir::Ty::Item(item) => {
                let field_map = self.get_struct_field_map(item)?;
                let field = field_map.get(field).ok_or_else(|| {
                    self.diag
                        .err(CodeErrorKind::UnresolvedItem(field.to_string()))
                })?;

                let mut obj = obj;
                while let ir::Ty::Pointer(_, _) = obj.ty {
                    obj = self.exprs.deref(obj, ast_span);
                }

                self.exprs.field(obj, field.id, field.ty, ast_span)
            }
            _ => return Err(self.diag.err(CodeErrorKind::StructLikeExpectedHere)),
        };

        Ok(result)
    }

    fn lower_index(
        &mut self,
        indexee: ast::ExprP<'ast>,
        index: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // We put usize as a hint, lower_range has a special case and will take
        let index = self.lower_expr(index, Some(self.types.builtin(BuiltinType::USize)))?;
        let indexee_hint = if let Some(LangTypeKind::Range(bound_ty)) =
            self.mono_ctx.get_lang_type_kind(index.ty)
        {
            if let ir::Ty::Builtin(BuiltinType::USize) = bound_ty {
                type_hint
            } else {
                return Err(mismatch!(
                    self,
                    self.types.builtin(BuiltinType::USize),
                    bound_ty
                ));
            }
        } else {
            type_hint.map(|ty| self.types.array(ty, 0))
        };

        let mut indexee = self.lower_expr(indexee, indexee_hint)?;

        if indexee.diverges() || index.diverges() {
            return Ok(self.exprs.diverges([indexee, index], ast_span));
        }

        // Special case for direct indexing of arrays, this is needed to break potential
        // circular references in the slice implementation. If the indexee is not an array,
        // we will try to coerce it into a slice and then index it.
        if matches!(indexee.ty, ir::Ty::Array(_, _)) {
            if let Ok(index) = self.try_coerce(self.types.builtin(BuiltinType::USize), index) {
                return Ok(self.exprs.index(indexee, index, ast_span));
            }
        }

        let ptr_ty = if let Some(LangTypeKind::Slice(ptr_ty)) =
            self.mono_ctx.get_lang_type_kind(indexee.ty)
        {
            ptr_ty
        } else {
            // Try slicifying the indexee

            let canonical = indexee.ty.canonical_type();
            indexee = self.autoref(indexee, self.types.pointer(canonical, true), ast_span)?;

            let item = self
                .monomorphize_lang_item(LangItemKind::SliceSlicify, [canonical, indexee.ty])
                .map_err(|_| mismatch!(self, "slice", indexee.ty))?;

            let func = self.exprs.function(item, ast_span);
            indexee = self.call(
                func,
                [indexee].into_iter(),
                item.get_function()
                    .map_err(|e| self.diag.err(e))?
                    .return_type,
                ast_span,
            )?;

            if let Some(LangTypeKind::Slice(ptr_ty)) = self.mono_ctx.get_lang_type_kind(indexee.ty)
            {
                ptr_ty
            } else {
                ice!("slice_slicify did not return a slice");
            }
        };

        if let Some(LangTypeKind::Range(_)) = self.mono_ctx.get_lang_type_kind(index.ty) {
            let item =
                self.monomorphize_lang_item(LangItemKind::SliceRangeIndex, [ptr_ty, index.ty])?;
            let func = self.exprs.function(item, ast_span);
            self.call(
                func,
                [indexee, index].into_iter(),
                item.get_function()
                    .map_err(|e| self.diag.err(e))?
                    .return_type,
                ast_span,
            )
        } else {
            let index = self.try_coerce(self.types.builtin(BuiltinType::USize), index)?;
            let item = self.monomorphize_lang_item(LangItemKind::SliceIndex, [ptr_ty])?;
            let func = self.exprs.function(item, ast_span);
            let call = self.call(func, [indexee, index].into_iter(), ptr_ty, ast_span)?;
            return Ok(self.exprs.deref(call, ast_span));
        }
    }

    fn lower_range(
        &mut self,
        lower: Option<ast::ExprP<'ast>>,
        upper: Option<ast::ExprP<'ast>>,
        inclusive: bool,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let bound_hint = match type_hint {
            // Special case for range indexing
            Some(ir::Ty::Builtin(BuiltinType::USize)) => type_hint,
            Some(ty) => self.mono_ctx.get_lang_type_kind(ty).and_then(|kind| {
                if let LangTypeKind::Range(inner) = kind {
                    Some(inner)
                } else {
                    None
                }
            }),
            None => None,
        };

        let lower = lower.map(|e| self.lower_expr(e, bound_hint)).transpose()?;
        let upper = upper
            .map(|e| self.lower_expr(e, lower.map(|l| l.ty).or(bound_hint)))
            .transpose()?;

        let stack = [lower, upper].into_iter().flatten().collect::<Vec<_>>();

        if stack.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(stack, ast_span));
        }

        let bound_ty = lower
            .map(|l| l.ty)
            .or_else(|| upper.map(|u| u.ty))
            .or(bound_hint)
            .unwrap_or_else(|| self.types.builtin(BuiltinType::I32)); // Same as for unqualified integer literals

        let result = match (lower, upper) {
            (Some(lower), Some(upper)) => {
                let lower = self.try_coerce(bound_ty, lower)?;
                let upper = self.try_coerce(bound_ty, upper)?;

                let item = if inclusive {
                    self.monomorphize_lang_item(LangItemKind::RangeInclusiveNew, [bound_ty])?
                } else {
                    self.monomorphize_lang_item(LangItemKind::RangeNew, [bound_ty])?
                };
                let func = self.exprs.function(item, ast_span);

                self.call(
                    func,
                    [lower, upper].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                )?
            }
            (Some(lower), None) => {
                let lower = self.try_coerce(bound_ty, lower)?;

                let item = self.monomorphize_lang_item(LangItemKind::RangeFromNew, [bound_ty])?;
                let func = self.exprs.function(item, ast_span);

                self.call(
                    func,
                    [lower].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                )?
            }
            (None, Some(upper)) => {
                let upper = self.try_coerce(bound_ty, upper)?;

                let item = if inclusive {
                    self.monomorphize_lang_item(LangItemKind::RangeToInclusiveNew, [bound_ty])?
                } else {
                    self.monomorphize_lang_item(LangItemKind::RangeToNew, [bound_ty])?
                };
                let func = self.exprs.function(item, ast_span);

                self.call(
                    func,
                    [upper].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                )?
            }
            (None, None) => {
                let item = self.monomorphize_lang_item(LangItemKind::RangeFullNew, [bound_ty])?;
                let func = self.exprs.function(item, ast_span);

                self.call(
                    func,
                    [].into_iter(),
                    item.get_function()
                        .map_err(|e| self.diag.err(e))?
                        .return_type,
                    ast_span,
                )?
            }
        };

        Ok(result)
    }

    fn generate_defer_prologue(&self, statements: &mut Vec<ir::Statement<'ir>>) {
        let defer_context = self.defer_context.as_ref().unwrap();

        for (defer_flag, _) in defer_context.defered.iter() {
            statements.push(ir::Statement::Expression(
                self.exprs.assign(
                    self.exprs
                        .local(*defer_flag, self.types.builtin(BuiltinType::Bool), None),
                    self.exprs.literal(
                        Value::Bool(false),
                        self.types.builtin(BuiltinType::Bool),
                        None,
                    ),
                    None,
                ),
            ));
        }
    }

    fn generate_defer_epilogue(&self, statements: &mut Vec<ir::Statement<'ir>>) {
        let defer_context = self.defer_context.as_ref().unwrap();

        statements.push(ir::Statement::Label(defer_context.return_label));
        for (id, expr) in defer_context.defered.iter().rev() {
            statements.push(ir::Statement::Expression(
                self.exprs.if_then(
                    self.exprs
                        .local(*id, self.types.builtin(BuiltinType::Bool), None),
                    self.exprs.block(
                        [ir::Statement::Expression(expr)],
                        self.exprs
                            .void(self.types.void(), ir::ValueType::RValue, None),
                        None,
                    ),
                    self.exprs
                        .void(self.types.void(), ir::ValueType::RValue, None),
                    None,
                ),
            ));
        }
        statements.push(ir::Statement::Expression(
            self.exprs.ret(
                self.exprs
                    .local(defer_context.return_local, self.return_type.unwrap(), None),
                None,
            ),
        ));
    }

    fn make_return(
        &mut self,
        inner: ir::ExprP<'ir>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if inner.diverges() {
            return Ok(inner);
        }
        let inner = self.try_coerce(self.return_type.unwrap(), inner)?;

        match self.defer_context.as_ref() {
            None | Some(DeferContext { in_defer: true, .. }) => Ok(self.exprs.ret(inner, ast_span)),
            Some(ctx) => Ok(self.exprs.block(
                [
                    ir::Statement::Expression(
                        self.exprs.assign(
                            self.exprs
                                .local(ctx.return_local, self.return_type.unwrap(), ast_span),
                            inner,
                            ast_span,
                        ),
                    ),
                    ir::Statement::Expression(self.exprs.goto(ctx.return_label, ast_span)),
                ],
                self.exprs.unreachable(ast_span),
                ast_span,
            )),
        }
    }

    fn lower_return(
        &mut self,
        inner: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.return_type.is_none() {
            return Err(self.diag.err(CodeErrorKind::NotInAFunctionScope));
        }

        let inner = inner
            .map(|inner| self.lower_expr(inner, self.return_type))
            .transpose()?
            .unwrap_or_else(|| {
                self.exprs
                    .void(self.types.void(), ir::ValueType::RValue, ast_span)
            });

        self.make_return(inner, ast_span)
    }

    fn lower_defer(
        &mut self,
        inner: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.return_type.is_none() {
            return Err(self.diag.err(CodeErrorKind::NotInAFunctionScope));
        }

        if !self.loop_contexts.is_empty() && !self.tentative {
            self.diag.warn(CodeErrorKind::DeferInALoop);
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
            Some(ctx) if ctx.in_defer => return Err(self.diag.err(CodeErrorKind::DeferInDefer)),
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
                .local(defer_flag, self.types.builtin(BuiltinType::Bool), ast_span),
            self.exprs.literal(
                Value::Bool(true),
                self.types.builtin(BuiltinType::Bool),
                ast_span,
            ),
            ast_span,
        ))
    }

    fn lower_struct(
        &mut self,
        typ: ast::TyP<'ast>,
        inits: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
        span: Option<ast::Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item = self.try_resolve_struct(typ, inits, type_hint)?;

        let field_map = self.get_struct_field_map(item)?;
        let mut uninitialized: HashSet<&'ast str> = field_map.keys().copied().collect();

        let lowered = inits
            .iter()
            .map(|f| {
                let _guard = self.diag.push_span(f.span);

                uninitialized.remove(f.name);
                match field_map.get(&f.name) {
                    Some(field) => self
                        .lower_expr(f.value, Some(field.ty))
                        .and_then(|e| self.try_coerce(field.ty, e))
                        .map(|i| (*field, i)),
                    None => Err(self
                        .diag
                        .err(CodeErrorKind::UnresolvedItem(f.name.to_string()))),
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        if lowered.iter().any(|(_, e)| e.diverges()) {
            return Ok(self
                .exprs
                .diverges(lowered.into_iter().map(|(_, e)| e), span));
        }

        let struct_type = self.types.named(item);
        let ret = self.exprs.r#struct(
            lowered.into_iter().map(|(f, e)| (f.id, e)).into_iter(),
            struct_type,
            span,
        );

        if !item
            .get_struct_like()
            .map_err(|e| self.diag.err(e))?
            .is_union
            && !self.tentative
        {
            for u in uninitialized {
                self.diag
                    .warn(CodeErrorKind::UninitializedField(u.to_string()));
            }
        }

        Ok(ret)
    }

    fn lower_array_expression(
        &mut self,
        elements: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let element_type_hint = match type_hint {
            Some(ir::Ty::Array(item, _)) => Some(*item),
            _ => None,
        };

        let mut first_elem_type = None;
        let mut lowered = Vec::new();
        for expr in elements {
            let expr = self.lower_expr(expr, first_elem_type.or(element_type_hint))?;
            if first_elem_type.is_none() {
                first_elem_type = Some(expr.ty);
            }
            lowered.push(self.try_coerce(first_elem_type.unwrap(), expr)?);
        }

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(lowered.into_iter(), ast_span));
        }

        let element_type = first_elem_type
            .or(element_type_hint)
            .ok_or_else(|| self.diag.err(CodeErrorKind::TypeInferenceFailed))?;

        self.array_of(element_type, lowered, ast_span)
    }

    fn lower_enum_value(
        &mut self,
        typ: ast::ItemP<'ast>,
        id: ast::AstId,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.monomorphize_item(typ, &[])?;
        let ir_id = self.mono_ctx.map_id(id);
        let result = match item_cell.get() {
            Ok(ir::IRItem::Enum(item)) => {
                let typ = self.types.named(item_cell);
                self.exprs.cast(
                    item.members.iter().find(|v| v.id == ir_id).unwrap().value,
                    typ,
                    ast_span,
                )
            }
            _ => return Err(self.diag.err(CodeErrorKind::CycleDetected)),
        };

        Ok(result.alloc_on(self.mono_ctx.ir))
    }

    fn lower_defered(
        &mut self,
        spec: &ast::Defered<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let typ = self.resolve_ast_type(spec.typ)?;
        // Currently only enum members can be defered during name/scope resolution (type::enum_value),
        // if it is not an enum, we assume it's an associated function. In the future there may be more
        // associated items that need to be handled.

        // Enum members have precedence over associated functions, but if the syntax indicates that
        // it is something that will be called (e.g. by calling it or specifying generic arguments),
        // it will be assumed to be a function, so there is some limited ambiguity.
        if let ast::Ty::Item(item) = typ {
            if let ast::Item::Enum(en) = item.get() {
                if let Some(id) = en
                    .members
                    .iter()
                    .find(|v| v.name == spec.name)
                    .map(|v| v.id)
                {
                    return self.lower_enum_value(item, id, type_hint, ast_span);
                }
            }
        }

        self.lower_fn(ast::FnKind::Defered(*spec), None, type_hint, ast_span)
    }

    fn lower_expr(
        &mut self,
        expr: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let _guard = self.diag.push_span(expr.span);

        match &expr.kind {
            ast::ExprKind::Void => {
                Ok(self
                    .exprs
                    .void(self.types.void(), ValueType::RValue, expr.span))
            }
            ast::ExprKind::Block(statements, ret) => {
                self.lower_block(statements, ret, type_hint, expr.span)
            }
            ast::ExprKind::Lit(lit) => self.lower_lit(lit, type_hint, expr.span),
            ast::ExprKind::Deref(expr) => self.lower_deref(expr, type_hint, expr.span),
            ast::ExprKind::Ref(expr) => self.lower_ref(expr, type_hint, expr.span),
            ast::ExprKind::Local(id) => self.lower_local(*id, type_hint, expr.span),
            ast::ExprKind::Unary(op, inner) => self.lower_unary(*op, inner, type_hint, expr.span),
            ast::ExprKind::Assign(lhs, rhs) => self.lower_assign(lhs, rhs, type_hint, expr.span),
            ast::ExprKind::If(cond, then, els) => {
                self.lower_if(cond, then, els, type_hint, expr.span)
            }
            ast::ExprKind::Cast(expr, typ) => self.lower_cast(expr, typ, type_hint, expr.span),
            ast::ExprKind::Loop(body) => self.lower_loop(body, type_hint, expr.span),
            ast::ExprKind::Binary(op, lhs, rhs) => {
                self.lower_binary(*op, lhs, rhs, type_hint, expr.span)
            }
            ast::ExprKind::AssignOp(op, lhs, rhs) => {
                self.lower_assign_op(*op, lhs, rhs, type_hint, expr.span)
            }
            ast::ExprKind::Break(value) => self.lower_break(*value, type_hint, expr.span),
            ast::ExprKind::Defer(value) => self.lower_defer(value, type_hint, expr.span),
            ast::ExprKind::Continue => self.lower_continue(type_hint, expr.span),
            ast::ExprKind::Tuple(exprs) => self.lower_tuple(exprs, type_hint, expr.span),
            ast::ExprKind::TupleIndex(tup, index) => {
                self.lower_tuple_index(tup, *index, type_hint, expr.span)
            }
            ast::ExprKind::Field(tup, field, _) => {
                self.lower_field(tup, field, type_hint, expr.span)
            }
            ast::ExprKind::Call(func, args) => self.lower_call(func, args, type_hint, expr.span),
            ast::ExprKind::Array(elements) => {
                self.lower_array_expression(elements, type_hint, expr.span)
            }
            ast::ExprKind::EnumValue(typ, id) => {
                self.lower_enum_value(typ, *id, type_hint, expr.span)
            }
            ast::ExprKind::Struct(func, initializers) => {
                self.lower_struct(func, initializers, type_hint, expr.span)
            }
            ast::ExprKind::Index(inner, index) => {
                self.lower_index(inner, index, type_hint, expr.span)
            }
            ast::ExprKind::Range(lower, upper, inclusive) => {
                self.lower_range(*lower, *upper, *inclusive, type_hint, expr.span)
            }
            ast::ExprKind::Return(inner) => self.lower_return(*inner, type_hint, expr.span),
            ast::ExprKind::Fn(item, args) => {
                self.lower_fn(item.clone(), *args, type_hint, expr.span)
            }
            ast::ExprKind::Static(item, args) => {
                self.lower_static(item, *args, type_hint, expr.span)
            }
            ast::ExprKind::Const(item, args) => self.lower_const(item, *args, type_hint, expr.span),
            ast::ExprKind::Defered(def) => self.lower_defered(def, type_hint, expr.span),
            ast::ExprKind::StaticIf(cond, then, els) => {
                self.lower_static_if(cond, then, els, type_hint, expr.span)
            }

            ast::ExprKind::BoundParam(self_arg, field_id, bound_type) => {
                self.lower_bound_param(*self_arg, *field_id, *bound_type, type_hint, expr.span)
            }
            ast::ExprKind::EtCetera(_) => ice!("macros should have been expanded by now"),
            ast::ExprKind::DeferedMacro(_, _) => ice!("macros should have been expanded by now"),
        }
    }
}

/// Intrinsic functions
impl<'a, 'ast, 'ir> Monomorphizer<'a, 'ast, 'ir> {
    fn get_const_string(&self, expr: ir::ExprP<'ir>) -> Result<&'ir str, AluminaError> {
        match ir::const_eval::ConstEvaluator::new(self.diag.fork(), self.mono_ctx.ir, [])
            .const_eval(expr)
        {
            Ok(value) => {
                if let Some(r) = extract_constant_string_from_slice(&value) {
                    Ok(std::str::from_utf8(r).unwrap())
                } else {
                    Err(mismatch!(self, "constant string", expr.ty))
                }
            }
            Err(e) => Err(e),
        }
    }

    fn align_of(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let align = self.mono_ctx.layouter.layout_of(ty)?.align;

        Ok(self.exprs.literal(
            Value::USize(align),
            self.types.builtin(BuiltinType::USize),
            span,
        ))
    }

    fn size_of(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let size = self.mono_ctx.layouter.layout_of(ty)?.size;

        Ok(self.exprs.literal(
            Value::USize(size),
            self.types.builtin(BuiltinType::USize),
            span,
        ))
    }

    fn type_id(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // just in case someone made a copy
        let interned = self.mono_ctx.ir.intern_type(*ty);

        // This will obviously not be stable between compilations, but for
        // now it's fine since we always monomorphize everything. Needs to be
        // retought if incremental compilation is ever implemented.
        let id = interned as *const ir::Ty<'ir> as usize;

        Ok(self.exprs.literal(
            Value::USize(id),
            self.types.builtin(BuiltinType::USize),
            span,
        ))
    }

    fn array_length_of(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if let ir::Ty::Array(_, len) = ty {
            return Ok(self.exprs.literal(
                Value::USize(*len),
                self.types.builtin(BuiltinType::USize),
                span,
            ));
        }

        Err(self.diag.err(CodeErrorKind::TypeMismatch(
            "array".to_string(),
            format!("{:?}", ty),
        )))
    }

    fn compile_fail(
        &self,
        reason: ir::ExprP<'ir>,
        _span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let reason = self.get_const_string(reason)?;

        Err(self
            .diag
            .err(CodeErrorKind::UserDefined(reason.to_string())))
    }

    fn compile_warn(
        &self,
        reason: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let reason = self.get_const_string(reason)?;

        self.diag
            .warn(CodeErrorKind::UserDefined(reason.to_string()));

        Ok(self.exprs.void(self.types.void(), ValueType::RValue, span))
    }

    fn compile_note(
        &self,
        reason: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let reason = self.get_const_string(reason)?;

        self.diag
            .note(CodeErrorKind::UserDefined(reason.to_string()));

        Ok(self.exprs.void(self.types.void(), ValueType::RValue, span))
    }

    fn unreachable(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.unreachable(span))
    }

    fn trap(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
        let ret_type = self.types.builtin(BuiltinType::Never);
        let fn_type = self.types.function([], ret_type);

        Ok(self.exprs.call(
            self.exprs.codegen_intrinsic(
                IntrinsicValueKind::FunctionLike("__builtin_trap"),
                fn_type,
                span,
            ),
            [],
            ret_type,
            span,
        ))
    }

    fn codegen_func(
        &self,
        name: ir::ExprP<'ir>,
        args: &[ir::ExprP<'ir>],
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.get_const_string(name)?;

        let arg_types = args.iter().map(|arg| arg.ty).collect::<Vec<_>>();
        let fn_type = self.types.function(arg_types, ret_ty);

        Ok(self.exprs.call(
            self.exprs
                .codegen_intrinsic(IntrinsicValueKind::FunctionLike(name), fn_type, span),
            args.iter().copied(),
            ret_ty,
            span,
        ))
    }

    fn codegen_type_func(
        &self,
        name: ir::ExprP<'ir>,
        ty: ir::TyP<'ir>,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.get_const_string(name)?;

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::SizeOfLike(name, ty), ret_ty, span))
    }

    fn asm(
        &self,
        assembly: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let assembly = self.get_const_string(assembly)?;

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::Asm(assembly), self.types.void(), span))
    }

    fn codegen_const(
        &self,
        name: ir::ExprP<'ir>,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.get_const_string(name)?;

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::ConstLike(name), ret_ty, span))
    }

    fn uninitialized(
        &self,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::Uninitialized, ret_ty, span))
    }

    fn dangling(
        &self,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if let ir::Ty::Pointer(inner, _) = ret_ty {
            Ok(self
                .exprs
                .codegen_intrinsic(IntrinsicValueKind::Dangling(inner), ret_ty, span))
        } else {
            Err(self.diag.err(CodeErrorKind::TypeMismatch(
                "pointer".to_string(),
                format!("{:?}", ret_ty),
            )))
        }
    }

    fn in_const_context(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.codegen_intrinsic(
            IntrinsicValueKind::InConstContext,
            self.types.builtin(BuiltinType::Bool),
            span,
        ))
    }
}

fn extract_constant_string_from_slice<'ir>(value: &Value<'ir>) -> Option<&'ir [u8]> {
    match value {
        Value::Struct(fields) => {
            let mut buf = None;
            let mut len = None;
            for (_id, value) in fields.iter() {
                if let Value::Str(r, offset) = value {
                    buf = r.get(*offset..);
                }
                if let Value::USize(len_) = value {
                    len = Some(*len_);
                }
            }

            if let (Some(buf), Some(len)) = (buf, len) {
                Some(&buf[..len])
            } else {
                None
            }
        }
        _ => None,
    }
}
