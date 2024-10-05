use crate::ast::lang::Lang;
use crate::ast::rebind::Rebinder;
use crate::ast::{Attribute, BuiltinType, Span};
use crate::common::{
    ice, AluminaError, ArenaAllocatable, CodeDiagnostic, CodeErrorBuilder, CycleGuardian, HashMap,
    HashSet, Marker,
};
use crate::diagnostics::DiagnosticsStack;
use crate::global_ctx::GlobalCtx;
use crate::ir::builder::{ExpressionBuilder, TypeBuilder};
use crate::ir::const_eval::{numeric_of_kind, ConstEvalErrorKind, Value};
use crate::ir::fold::{Folder, IdUsageCounter};
use crate::ir::infer::TypeInferer;
use crate::ir::inline::IrInliner;
use crate::ir::{FuncBody, ItemP, LocalDef, ValueType};
use crate::src::scope::BoundItemType;
use crate::{ast, ir};

use once_cell::unsync::OnceCell;
use std::backtrace::Backtrace;

use std::collections::hash_map::Entry;
use std::iter::once;
use std::ops::{Bound, RangeBounds};
use std::rc::Rc;

use super::const_eval::MallocBag;
use super::layout::Layouter;
use super::{LangKind, RangeKind};

pub mod intrinsics;

macro_rules! mismatch {
    ($self:expr, $expected:literal, $actual:expr) => {
        $self.diag.err(crate::common::CodeDiagnostic::TypeMismatch(
            format!("{}", $expected),
            $self.ctx.type_name($actual).unwrap(),
        ))
    };

    ($self:expr, $expected:expr, $actual:expr) => {
        $self.diag.err(crate::common::CodeDiagnostic::TypeMismatch(
            $self.ctx.type_name($expected).unwrap(),
            $self.ctx.type_name($actual).unwrap(),
        ))
    };
}
pub(crate) use mismatch;

macro_rules! bail {
    ($self:expr, $kind:expr) => {
        return Err($self.diag.err($kind))
    };
}
pub(crate) use bail;

#[derive(Default)]
pub struct Caches<'ast, 'ir> {
    associated_fns: HashMap<ir::TyP<'ir>, Rc<HashMap<&'ast str, ast::ItemP<'ast>>>>,
    associated_fns_ast: HashMap<ast::TyP<'ast>, Rc<HashMap<&'ast str, ast::ItemP<'ast>>>>,
    struct_field_maps: HashMap<ir::ItemP<'ir>, Rc<HashMap<&'ast str, &'ir ir::Field<'ir>>>>,
    protocol_bound_matches: HashMap<(ir::TyP<'ir>, ir::TyP<'ir>), BoundCheckResult>,
}

pub struct MonoCtx<'ast, 'ir> {
    ast: &'ast ast::AstCtx<'ast>,
    ir: &'ir ir::IrCtx<'ir>,
    layouter: Layouter<'ir>,
    global_ctx: GlobalCtx,
    id_map: HashMap<ast::Id, ir::Id>,
    cycles: CycleGuardian<(ast::ItemP<'ast>, &'ir [ir::TyP<'ir>])>,
    finished: HashMap<MonoKey<'ast, 'ir>, ir::ItemP<'ir>>,
    reverse_map: HashMap<ir::ItemP<'ir>, MonoKey<'ast, 'ir>>,
    static_local_defs: HashMap<ir::ItemP<'ir>, Vec<LocalDef<'ir>>>,
    vtable_layouts: HashMap<&'ir [ir::TyP<'ir>], ir::VtableLayout<'ir>>,
    static_inits: Vec<ir::ItemP<'ir>>,
    malloc_bag: MallocBag<'ir>,
    caches: Caches<'ast, 'ir>,
}

#[derive(Clone)]
enum BoundCheckResult {
    Matches,
    DoesNotMatch,
    DoesNotMatchBecause(String),
}

enum TupleIndex {
    Single(usize),
    Range(Bound<usize>, Bound<usize>),
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
            global_ctx,
            id_map: HashMap::default(),
            finished: HashMap::default(),
            reverse_map: HashMap::default(),
            static_local_defs: HashMap::default(),
            cycles: CycleGuardian::new(),
            vtable_layouts: HashMap::default(),
            malloc_bag: MallocBag::new(),
            static_inits: Vec::new(),
            caches: Caches::default(),
        }
    }

    fn map_id(&mut self, id: ast::Id) -> ir::Id {
        *self.id_map.entry(id).or_insert_with(|| self.ir.make_id())
    }

    pub fn reverse_lookup(&self, item: ir::ItemP<'ir>) -> MonoKey<'ast, 'ir> {
        self.reverse_map
            .get(&item)
            .cloned()
            .expect("reverse lookup failed")
    }

    fn map_attribute(&self, attr: &ast::Attribute<'ast>) -> ast::Attribute<'ir> {
        match attr {
            Attribute::Export => Attribute::Export,
            Attribute::Cold => Attribute::Cold,
            Attribute::TestMain => Attribute::TestMain,
            Attribute::Main => Attribute::Main,
            Attribute::Inline(k) => Attribute::Inline(*k),
            Attribute::Align(i) => Attribute::Align(*i),
            Attribute::Packed(i) => Attribute::Packed(*i),
            Attribute::TupleCall => Attribute::TupleCall,
            Attribute::ConstOnly => Attribute::ConstOnly,
            Attribute::NoConst => Attribute::NoConst,
            Attribute::Diagnostic(k) => Attribute::Diagnostic(*k),
            Attribute::Transparent => Attribute::Transparent,
            Attribute::ThreadLocal => Attribute::ThreadLocal,
            Attribute::Builtin => Attribute::Builtin,
            Attribute::Intrinsic => Attribute::Intrinsic,
            Attribute::StaticConstructor => Attribute::StaticConstructor,
            Attribute::LinkName(s) => Attribute::LinkName(s.alloc_on(self.ir)),
            Attribute::Coroutine => Attribute::Coroutine,
            Attribute::Custom(v) => Attribute::Custom(self.map_custom_attribute(v)),
        }
    }

    fn map_custom_attribute(&self, attr: &ast::CustomAttribute<'ast>) -> ast::CustomAttribute<'ir> {
        ast::CustomAttribute {
            name: attr.name.alloc_on(self.ir),
            values: self
                .ir
                .arena
                .alloc_slice_fill_iter(attr.values.iter().map(|v| match v {
                    ast::CustomAttributeValue::Attribute(a) => {
                        ast::CustomAttributeValue::Attribute(self.map_custom_attribute(a))
                    }
                    ast::CustomAttributeValue::Value(l) => {
                        ast::CustomAttributeValue::Value(match l {
                            ast::Lit::Str(s) => ast::Lit::Str(self.ir.arena.alloc_slice_copy(s)),
                            ast::Lit::Int(a, b, _) => ast::Lit::Int(*a, *b, None),
                            _ => unreachable!(),
                        })
                    }
                })),
        }
    }

    pub fn lang_type_kind(&self, ty: ir::TyP<'ir>) -> Option<LangKind<'ir>> {
        let item = match ty {
            ir::Ty::Item(item) => item,
            _ => return None,
        };

        let item = self.reverse_lookup(item);
        if self.ast.lang_item(Lang::Slice).ok() == Some(item.0) {
            return Some(LangKind::Slice(item.1[0]));
        }

        if self.ast.lang_item(Lang::RangeFull).ok() == Some(item.0) {
            return Some(LangKind::Range(item.1[0], RangeKind::RangeFull));
        }

        if self.ast.lang_item(Lang::RangeFrom).ok() == Some(item.0) {
            return Some(LangKind::Range(item.1[0], RangeKind::RangeFrom));
        }

        if self.ast.lang_item(Lang::RangeTo).ok() == Some(item.0) {
            return Some(LangKind::Range(item.1[0], RangeKind::RangeTo));
        }

        if self.ast.lang_item(Lang::RangeToInclusive).ok() == Some(item.0) {
            return Some(LangKind::Range(item.1[0], RangeKind::RangeToInclusive));
        }

        if self.ast.lang_item(Lang::Range).ok() == Some(item.0) {
            return Some(LangKind::Range(item.1[0], RangeKind::Range));
        }

        if self.ast.lang_item(Lang::RangeInclusive).ok() == Some(item.0) {
            return Some(LangKind::Range(item.1[0], RangeKind::RangeInclusive));
        }

        if self.ast.lang_item(Lang::Dyn).ok() == Some(item.0) {
            return Some(LangKind::Dyn(item.1[0], item.1[1]));
        }

        if self.ast.lang_item(Lang::DynSelf).ok() == Some(item.0) {
            return Some(LangKind::DynSelf);
        }

        if self.ast.lang_item(Lang::ProtoCallable).ok() == Some(item.0) {
            if let ir::Ty::Tuple(args) = item.1[0] {
                return Some(LangKind::ProtoCallable(
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

    fn type_name(&self, ty: ir::TyP<'ir>) -> Result<String, AluminaError> {
        use ir::Ty::*;
        use std::fmt::Write;

        let mut f = String::new();

        match ty {
            Item(cell) => {
                let MonoKey(cell, args, _, _) = self.reverse_lookup(cell);

                match self.lang_type_kind(ty) {
                    Some(LangKind::Dyn(ir::Ty::Tuple(protos), ir::Ty::Pointer(_, is_const))) => {
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

                    Some(LangKind::Slice(ir::Ty::Pointer(inner, is_const))) => {
                        if *is_const {
                            let _ = write!(f, "&[{}]", self.type_name(inner)?);
                        } else {
                            let _ = write!(f, "&mut [{}]", self.type_name(inner)?);
                        }
                        return Ok(f);
                    }

                    Some(LangKind::ProtoCallable(args, ret)) => {
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
                    ast::Item::StaticOrConst(e) => {
                        write!(f, "{}", e.name.unwrap_or("{{anonymous}}"))
                    }
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
    loop_result: ir::Id,
    break_label: ir::Id,
    continue_label: ir::Id,
}

#[derive(Debug, Clone)]
pub struct DeferContext<'ir> {
    defered: Vec<(ir::Id, ir::ExprP<'ir>)>,
    in_defer: bool,
    return_label: ir::Id,
    return_local: ir::Id,
}

impl DeferContext<'_> {
    fn new(return_label: ir::Id, return_local: ir::Id) -> Self {
        DeferContext {
            defered: Vec::new(),
            in_defer: false,
            return_label,
            return_local,
        }
    }
}

pub struct Mono<'a, 'ast, 'ir> {
    ctx: &'a mut MonoCtx<'ast, 'ir>,
    exprs: ExpressionBuilder<'ir>,
    types: TypeBuilder<'ir>,
    current: Option<ItemP<'ir>>,
    replacements: HashMap<ast::Id, ir::TyP<'ir>>,
    return_type: Option<ir::TyP<'ir>>,
    yield_type: Option<ir::TyP<'ir>>,
    recv_type: Option<ir::TyP<'ir>>,
    loop_contexts: Vec<LoopContext<'ir>>,
    local_types: HashMap<ir::Id, ir::TyP<'ir>>,
    local_type_hints: HashMap<ir::Id, ir::TyP<'ir>>,
    local_defs: Vec<ir::LocalDef<'ir>>,
    const_replacements: HashMap<ir::Id, Value<'ir>>,
    defer_context: Option<DeferContext<'ir>>,
    diag: DiagnosticsStack,
    tentative: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonoKey<'ast, 'ir>(
    pub ast::ItemP<'ast>,
    pub &'ir [ir::TyP<'ir>],
    pub Option<ir::Id>,
    pub bool,
);

impl<'ast, 'ir> MonoKey<'ast, 'ir> {
    fn new(
        item: ast::ItemP<'ast>,
        tys: &'ir [ir::TyP<'ir>],
        index: Option<ir::Id>,
        tentative: bool,
    ) -> Self {
        MonoKey(item, tys, index, tentative)
    }
}

impl<'a, 'ast, 'ir> Mono<'a, 'ast, 'ir> {
    pub fn new<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        tentative: bool,
        parent_item: Option<ItemP<'ir>>,
    ) -> Mono<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        let diag = mono_ctx.global_ctx.diag().clone();
        Mono {
            ctx: mono_ctx,
            replacements: HashMap::default(),
            local_types: HashMap::default(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: None,
            yield_type: None,
            recv_type: None,
            loop_contexts: Vec::new(),
            local_type_hints: HashMap::default(),
            local_defs: Vec::new(),
            const_replacements: HashMap::default(),
            defer_context: None,
            tentative,
            current: parent_item,
            diag: DiagnosticsStack::new(diag),
        }
    }

    fn with_replacements<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        replacements: HashMap<ast::Id, ir::TyP<'ir>>,
        tentative: bool,
        parent_item: Option<ItemP<'ir>>,
        diag_stack: DiagnosticsStack,
    ) -> Mono<'b, 'ast, 'ir> {
        let ir = mono_ctx.ir;
        Mono {
            ctx: mono_ctx,
            replacements,
            local_types: HashMap::default(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: None,
            yield_type: None,
            recv_type: None,
            loop_contexts: Vec::new(),
            local_defs: Vec::new(),
            local_type_hints: HashMap::default(),
            const_replacements: HashMap::default(),
            defer_context: None,
            tentative,
            current: parent_item,
            diag: diag_stack,
        }
    }

    fn mono_enum(
        &mut self,
        item: ir::ItemP<'ir>,
        en: &ast::Enum<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(en.span);

        if !generic_args.is_empty() {
            bail!(
                self,
                CodeDiagnostic::GenericParamCountMismatch(0, generic_args.len())
            );
        }

        let mut members = Vec::new();
        let mut child = Self::new(self.ctx, self.tentative, self.current);
        let mut type_hint = None;
        let mut taken_values = HashSet::default();

        let (valued, non_valued): (Vec<_>, Vec<_>) =
            en.members.iter().copied().partition(|m| m.value.is_some());
        let mut evaluator = ir::const_eval::ConstEvaluator::new(
            child.ctx.global_ctx.clone(),
            child.diag.fork(),
            child.ctx.malloc_bag.clone(),
            child.ctx.ir,
            child.local_types.iter().map(|(k, v)| (*k, *v)),
        );

        for m in valued {
            let _guard = self.diag.push_span(m.span);

            let expr = child.lower_expr(m.value.unwrap(), type_hint)?;
            match expr.ty {
                ir::Ty::Builtin(b) if b.is_integer() => {}
                _ => bail!(self, CodeDiagnostic::InvalidValueForEnumVariant),
            };

            let value = evaluator.const_eval(expr)?;
            if !type_hint.get_or_insert(expr.ty).assignable_from(expr.ty) {
                return Err(mismatch!(self, type_hint.unwrap(), expr.ty));
            }

            if !taken_values.insert(value) {
                ice!(self.diag, "duplicate enum member");
            }

            members.push(ir::EnumMember {
                id: child.ctx.map_id(m.id),
                name: m.name.alloc_on(child.ctx.ir),
                value: child.exprs.literal(value, expr.ty, m.span),
            });
        }

        // Populate the enum members without values
        let kind = match type_hint.get_or_insert(child.types.builtin(BuiltinType::I32)) {
            ir::Ty::Builtin(k) => *k,
            _ => unreachable!(),
        };
        let enum_type = type_hint.unwrap();

        let mut counter = numeric_of_kind!(kind, 0);
        let mut seen = HashSet::default();
        for m in non_valued {
            let next_non_taken = loop {
                let _guard = self.diag.push_span(m.span);

                if taken_values.insert(counter) {
                    break counter;
                }
                counter = evaluator.const_eval(
                    self.exprs.binary(
                        ast::BinOp::Plus,
                        self.exprs.literal(counter, enum_type, m.span),
                        self.exprs
                            .literal(numeric_of_kind!(kind, 1), enum_type, m.span),
                        enum_type,
                        m.span,
                    ),
                )?;
                // We wrapped around, the enum is full
                if !seen.insert(counter) {
                    return Err(self.diag.err(CodeDiagnostic::TooManyEnumVariants(
                        child.ctx.type_name(enum_type)?,
                    )));
                }
            };

            members.push(ir::EnumMember {
                id: child.ctx.map_id(m.id),
                name: m.name.alloc_on(child.ctx.ir),
                value: self.exprs.literal(next_non_taken, enum_type, m.span),
            });
        }

        let res = ir::Item::Enum(ir::Enum {
            name: en.name.map(|n| n.alloc_on(child.ctx.ir)),
            underlying_ty: enum_type,
            members: members.alloc_on(child.ctx.ir),
            attributes: en
                .attributes
                .iter()
                .map(|a| child.ctx.map_attribute(a))
                .collect::<Vec<_>>()
                .alloc_on(child.ctx.ir),
            span: en.span,
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
    ) -> Result<HashMap<ast::Id, ir::TyP<'ir>>, AluminaError> {
        if generic_args.len() != placeholders.len() {
            bail!(
                self,
                CodeDiagnostic::GenericParamCountMismatch(placeholders.len(), generic_args.len())
            );
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

    fn mono_struct(
        &mut self,
        item: ir::ItemP<'ir>,
        s: &ast::StructLike<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.ctx,
            replacements,
            self.tentative,
            self.current,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.ty)?;
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
                    id: child.ctx.map_id(f.id),
                    name: Some(f.name.alloc_on(child.ctx.ir)),
                    ty: child.lower_type_for_value(f.ty)?,
                })
            })
            .collect::<Result<Vec<_>, AluminaError>>()?;

        let attributes = s
            .attributes
            .iter()
            .map(|a| child.ctx.map_attribute(a))
            .collect::<Vec<_>>();

        let res = ir::Item::StructLike(ir::StructLike {
            name: s.name.map(|n| n.alloc_on(child.ctx.ir)),
            fields: fields.alloc_on(child.ctx.ir),
            attributes: attributes.alloc_on(child.ctx.ir),
            is_union: s.is_union,
            span: s.span,
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

    fn mono_typedef(
        &mut self,
        item: ir::ItemP<'ir>,
        s: &ast::TypeDef<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.ctx,
            replacements,
            self.tentative,
            self.current,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.ty)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let target = s
            .target
            .ok_or_else(|| self.diag.err(CodeDiagnostic::TypedefWithoutTarget))?;

        let inner = child.lower_type_unrestricted(target)?;

        let res = ir::Item::Alias(inner);
        item.assign(res);

        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        Ok(())
    }

    fn mono_protocol(
        &mut self,
        item: ir::ItemP<'ir>,
        s: &ast::Protocol<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.ctx,
            replacements,
            self.tentative,
            self.current,
            self.diag.fork(),
        );

        // Protocols can have their own protocol bounds, yay!
        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.ty)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let mut methods = Vec::new();
        for m in s.associated_fns {
            let fun = m.item.get_function();
            if !fun.placeholders.is_empty() {
                bail!(self, CodeDiagnostic::MixinOnlyProtocol);
            }

            let mut param_types = Vec::new();
            for p in fun.args {
                param_types.push(child.lower_type_for_value(p.ty)?);
            }
            let ret = child.lower_type_for_value(fun.return_type)?;

            methods.push(ir::ProtocolFunction {
                name: m.name.alloc_on(child.ctx.ir),
                arg_types: param_types.alloc_on(child.ctx.ir),
                return_type: ret,
            });
        }

        let res = ir::Item::Protocol(ir::Protocol {
            name: s.name.map(|n| n.alloc_on(child.ctx.ir)),
            methods: methods.alloc_on(child.ctx.ir),
            attributes: s
                .attributes
                .iter()
                .map(|a| child.ctx.map_attribute(a))
                .collect::<Vec<_>>()
                .alloc_on(child.ctx.ir),
            span: s.span,
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
        ty: ir::TyP<'ir>,
        bounds: Vec<(Option<ast::Span>, ir::TyP<'ir>, bool)>,
    ) -> Result<(), AluminaError> {
        if bounds.is_empty() {
            return Ok(());
        }

        let mut found = false;
        for (span, bound, negated) in bounds.iter().copied() {
            let _guard = self.diag.push_span(span);

            match self.check_protocol_bound(bound, ty)? {
                BoundCheckResult::Matches if negated => {
                    if kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    if negated {
                        bail!(
                            self,
                            CodeDiagnostic::ProtocolMatch(
                                self.ctx.type_name(ty).unwrap(),
                                self.ctx.type_name(bound).unwrap()
                            )
                        );
                    }
                }
                BoundCheckResult::DoesNotMatch if !negated => {
                    if kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    bail!(
                        self,
                        CodeDiagnostic::ProtocolMismatch(
                            self.ctx.type_name(ty).unwrap(),
                            self.ctx.type_name(bound).unwrap()
                        )
                    );
                }
                BoundCheckResult::DoesNotMatchBecause(detail) if !negated => {
                    if kind == ast::ProtocolBoundsKind::Any {
                        continue;
                    }
                    bail!(
                        self,
                        CodeDiagnostic::ProtocolMismatchDetail(
                            self.ctx.type_name(ty).unwrap(),
                            self.ctx.type_name(bound).unwrap(),
                            detail
                        )
                    );
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

            bail!(
                self,
                CodeDiagnostic::ProtocolMismatch(
                    self.ctx.type_name(ty).unwrap(),
                    bounds
                        .iter()
                        .map(|(_, bound, negated)| if *negated {
                            format!("!{}", self.ctx.type_name(bound).unwrap())
                        } else {
                            self.ctx.type_name(bound).unwrap()
                        })
                        .collect::<Vec<_>>()
                        .join(" | ")
                )
            );
        }

        Ok(())
    }

    fn check_protocol_bound(
        &mut self,
        bound: ir::TyP<'ir>,
        ty: ir::TyP<'ir>,
    ) -> Result<BoundCheckResult, AluminaError> {
        if let Some(result) = self.ctx.caches.protocol_bound_matches.get(&(bound, ty)) {
            return Ok(result.clone());
        }

        let result = self.check_protocol_bound_uncached(bound, ty)?;
        self.ctx
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
                Ok(ir::Item::Protocol(_)) => protocol,
                Err(_) => bail!(self, CodeDiagnostic::CyclicProtocolBound),
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

        let MonoKey(ast_item, proto_generic_args, _, _) = self.ctx.reverse_lookup(protocol_item);
        match self.ctx.ast.lang_item_kind(ast_item) {
            Some(Lang::ProtoAny) => return Ok(BoundCheckResult::Matches),
            Some(Lang::ProtoNone) => return Ok(BoundCheckResult::DoesNotMatch),
            Some(Lang::ProtoZeroSized) => {
                let layout = self.ctx.layouter.layout_of(ty).with_backtrace(&self.diag)?;
                if layout.is_zero_sized() {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
            Some(Lang::ProtoTuple) => match ty {
                ir::Ty::Tuple(_) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoFloatingPoint) => match ty {
                ir::Ty::Builtin(k) if k.is_float() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoInteger) => match ty {
                ir::Ty::Builtin(k) if k.is_integer() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoNumeric) => match ty {
                ir::Ty::Builtin(k) if k.is_numeric() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoSigned) => match ty {
                ir::Ty::Builtin(k) if k.is_signed() => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoUnsigned) => match ty {
                ir::Ty::Builtin(k) if k.is_integer() && !k.is_signed() => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoPrimitive) => match ty {
                ir::Ty::Builtin(_) => return Ok(BoundCheckResult::Matches),
                ir::Ty::Pointer(_, _) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoStruct) => match ty {
                ir::Ty::Item(item) => match item.get() {
                    Ok(ir::Item::StructLike(s)) if !s.is_union => {
                        return Ok(BoundCheckResult::Matches)
                    }
                    _ => return Ok(BoundCheckResult::DoesNotMatch),
                },
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoUnion) => match ty {
                ir::Ty::Item(item) => match item.get() {
                    Ok(ir::Item::StructLike(s)) if s.is_union => {
                        return Ok(BoundCheckResult::Matches)
                    }
                    _ => return Ok(BoundCheckResult::DoesNotMatch),
                },
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoEnum) => match ty {
                ir::Ty::Item(item) => match item.get() {
                    Ok(ir::Item::Enum(_)) => return Ok(BoundCheckResult::Matches),
                    _ => return Ok(BoundCheckResult::DoesNotMatch),
                },
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoPointer) => match ty {
                ir::Ty::Pointer(_, _) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoArray) => match ty {
                ir::Ty::Array(_, _) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoRange) => match self.ctx.lang_type_kind(ty) {
                Some(LangKind::Range(..)) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoRangeOf) => match self.ctx.lang_type_kind(ty) {
                Some(LangKind::Range(k, _)) if k == proto_generic_args[0] => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoMeta) => match ty {
                ir::Ty::Item(item) if matches!(item.get(), Ok(ir::Item::Protocol(_))) => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoCallable) => {
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
                    ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag)? {
                        ir::Item::Closure(fun_item) => {
                            let fun = fun_item
                                .function
                                .get()
                                .unwrap()
                                .get_function()
                                .with_backtrace(&self.diag)?;
                            actual_args = fun.args.iter().skip(1).map(|arg| arg.ty).collect();
                            (&actual_args[..], fun.return_type)
                        }
                        ir::Item::Function(fun) => {
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
            Some(Lang::ProtoNamedFunction) => match ty {
                ir::Ty::Item(item)
                    if matches!(
                        item.get().with_backtrace(&self.diag)?,
                        ir::Item::Function(_)
                    ) =>
                {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoConst) => match ty {
                ir::Ty::Item(item)
                    if matches!(item.get().with_backtrace(&self.diag)?, ir::Item::Const(_)) =>
                {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoStatic) => match ty {
                ir::Ty::Item(item)
                    if matches!(item.get().with_backtrace(&self.diag)?, ir::Item::Static(_)) =>
                {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoFunctionPointer) => match ty {
                ir::Ty::FunctionPointer(..) => return Ok(BoundCheckResult::Matches),
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoClosure) => match ty {
                ir::Ty::Item(item)
                    if matches!(item.get().with_backtrace(&self.diag)?, ir::Item::Closure(_)) =>
                {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoArrayOf) => match ty {
                ir::Ty::Array(k, _) if *k == proto_generic_args[0] => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoPointerOf) => match ty {
                ir::Ty::Pointer(k, _) if *k == proto_generic_args[0] => {
                    return Ok(BoundCheckResult::Matches)
                }
                _ => return Ok(BoundCheckResult::DoesNotMatch),
            },
            Some(Lang::ProtoSameLayoutAs) => {
                let ty_layout = self.ctx.layouter.layout_of(ty).with_backtrace(&self.diag)?;
                let arg_layout = self
                    .ctx
                    .layouter
                    .layout_of(proto_generic_args[0])
                    .with_backtrace(&self.diag)?;

                if ty_layout.is_compatible_with(&arg_layout) {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
            Some(Lang::ProtoSameBaseAs) => {
                let ty_item = match ty {
                    ir::Ty::Item(i) => i,
                    _ => {
                        return Ok(BoundCheckResult::DoesNotMatchBecause(
                            "it is not a named type".into(),
                        ))
                    }
                };
                let param_item = match proto_generic_args[0] {
                    ir::Ty::Item(i) => i,
                    _ => {
                        return Ok(BoundCheckResult::DoesNotMatchBecause(format!(
                            "{} is not a named type",
                            self.ctx.type_name(proto_generic_args[0])?
                        )))
                    }
                };

                let MonoKey(ty_ast, _, _, _) = self.ctx.reverse_lookup(ty_item);
                let MonoKey(param_ast, _, _, _) = self.ctx.reverse_lookup(param_item);

                if ty_ast == param_ast {
                    return Ok(BoundCheckResult::Matches);
                } else {
                    return Ok(BoundCheckResult::DoesNotMatch);
                }
            }
            Some(_) | None => {}
        };

        // `&dyn Proto<...>` always satisfies Proto<...>
        if let Some(LangKind::Dyn(ir::Ty::Tuple(inner_tys), _)) = self.ctx.lang_type_kind(ty) {
            for inner_ty in inner_tys.iter() {
                if let ir::Ty::Item(inner_proto) = inner_ty {
                    let MonoKey(inner_ast, inner_args, ..) = self.ctx.reverse_lookup(inner_proto);

                    if ast_item == inner_ast
                        && proto_generic_args.first().copied() == Some(ty)
                        && proto_generic_args.get(1..) == inner_args.get(1..)
                    {
                        return Ok(BoundCheckResult::Matches);
                    }
                }
            }
        }

        let protocol = protocol_item.get_protocol().with_backtrace(&self.diag)?;
        let associated_fns = self.associated_fns(ty)?;

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
                self.ctx.ast,
                self.ctx.ir,
                self.ctx,
                candidate_fun.placeholders.to_vec(),
            );

            let infer_slots = candidate_fun
                .args
                .iter()
                .zip(proto_fun.arg_types.iter())
                .map(|(p, t)| (p.ty, *t))
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

            let monomorphized =
                match self.mono_item_uncached(None, item, generic_args.alloc_on(self.ctx.ir), true)
                {
                    Ok(mono) => mono.get_function().with_backtrace(&self.diag)?,
                    Err(AluminaError::CodeErrors(code))
                        if code.iter().all(|c| {
                            matches!(
                                c.kind,
                                CodeDiagnostic::ProtocolMatch(_, _)
                                    | CodeDiagnostic::ProtocolMismatch(_, _)
                                    | CodeDiagnostic::ProtocolMismatchDetail(_, _, _)
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

    fn mono_static_or_const(
        &mut self,
        item: ir::ItemP<'ir>,
        s: &ast::StaticOrConst<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push_span(s.span);

        let replacements = self.resolve_placeholders(s.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.ctx,
            replacements,
            self.tentative,
            self.current,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in s.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.ty)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        let ty = s.ty.map(|t| child.lower_type_for_value(t)).transpose()?;
        let mut init = s.init.map(|t| child.lower_expr(t, ty)).transpose()?;

        if s.is_const {
            let init = if let Some(ty) = ty {
                let init = init.unwrap();
                child.try_coerce(ty, init)?
            } else {
                init.unwrap()
            };

            let value = ir::const_eval::ConstEvaluator::new(
                child.ctx.global_ctx.clone(),
                child.diag.fork(),
                child.ctx.malloc_bag.clone(),
                child.ctx.ir,
                child.local_types.iter().map(|(k, v)| (*k, *v)),
            )
            .const_eval(init)?;

            let res = ir::Item::Const(ir::Const {
                name: s.name.map(|n| n.alloc_on(child.ctx.ir)),
                ty: init.ty,
                init: child.exprs.literal(value, init.ty, init.span),
                attributes: s
                    .attributes
                    .iter()
                    .map(|a| child.ctx.map_attribute(a))
                    .collect::<Vec<_>>()
                    .alloc_on(child.ctx.ir),
                span: s.span,
                value,
            });

            item.assign(res);
        } else {
            let ty = ty.or_else(|| init.map(|i| i.ty)).unwrap();
            if let Some(init) = &mut init {
                *init = child.try_coerce(ty, init)?;
            }

            let attributes = s
                .attributes
                .iter()
                .map(|a| child.ctx.map_attribute(a))
                .collect::<Vec<_>>();

            let res = ir::Item::Static(ir::Static {
                name: s.name.map(|n| n.alloc_on(child.ctx.ir)),
                ty,
                init,
                attributes: attributes.alloc_on(child.ctx.ir),
                span: s.span,
                r#extern: s.r#extern,
            });
            item.assign(res);
            child.ctx.static_inits.push(item);
            child.ctx.static_local_defs.insert(item, child.local_defs);
        }

        Ok(())
    }

    fn mono_function(
        &mut self,
        item: ir::ItemP<'ir>,
        key: MonoKey<'ast, 'ir>,
        signature_only: bool,
    ) -> Result<(), AluminaError> {
        let MonoKey(ast_item, generic_args, _, _) = key.clone();
        let func = ast_item.get_function();

        let _guard = self.diag.push_span(func.span);

        let replacements = self.resolve_placeholders(func.placeholders, generic_args)?;
        let mut child = Self::with_replacements(
            self.ctx,
            replacements,
            self.tentative,
            self.current,
            self.diag.fork(),
        );

        let mut protocol_bounds = Vec::new();
        for (placeholder, ty) in func.placeholders.iter().zip(generic_args.iter()) {
            let mut grouped_bounds = Vec::new();
            for bound in placeholder.bounds.bounds {
                let _guard = self.diag.push_span(bound.span);

                let ir_bound = child.lower_type_unrestricted(bound.ty)?;
                grouped_bounds.push((bound.span, ir_bound, bound.negated));
            }
            protocol_bounds.push((placeholder.bounds.kind, *ty, grouped_bounds));
        }

        let mut parameters = func
            .args
            .iter()
            .map(|p| {
                let param = ir::Parameter {
                    id: child.ctx.map_id(p.id),
                    ty: child.lower_type_for_value(p.ty)?,
                };
                child.local_types.insert(param.id, param.ty);
                Ok(param)
            })
            .collect::<Result<Vec<_>, AluminaError>>()?;

        let attributes = func
            .attributes
            .iter()
            .map(|a| child.ctx.map_attribute(a))
            .collect::<Vec<_>>();

        let return_type = child.lower_type_for_value(func.return_type)?;
        let tuple_args_arg = if attributes.contains(&ast::Attribute::TupleCall) {
            if parameters.len() != 1 {
                bail!(self, CodeDiagnostic::TupleCallArgCount);
            }

            let ir::Ty::Tuple(args) = parameters[0].ty else {
                bail!(self, CodeDiagnostic::TupleCallArgType);
            };

            let tuple_param = parameters[0];
            parameters = args
                .iter()
                .map(|ty| {
                    let param = ir::Parameter {
                        id: child.ctx.ir.make_id(),
                        ty,
                    };
                    child.local_types.insert(param.id, param.ty);
                    param
                })
                .collect();

            Some((tuple_param, &parameters[..]))
        } else {
            None
        };

        let parameters = (&parameters[..]).alloc_on(child.ctx.ir);
        let res = ir::Item::Function(ir::Function {
            name: func.name.map(|n| n.alloc_on(child.ctx.ir)),
            attributes: attributes.alloc_on(child.ctx.ir),
            args: parameters,
            varargs: func.varargs,
            span: func.span,
            return_type,
            body: OnceCell::new(),
        });
        item.assign(res);

        // This happens after we assign the signature to avoid issues when calling recursively
        for (kind, ty, bounds) in protocol_bounds {
            child.check_protocol_bounds(kind, ty, bounds)?;
        }

        let coroutine_types = if func.attributes.contains(&ast::Attribute::Coroutine) {
            match return_type {
                ir::Ty::Item(item) => {
                    let MonoKey(ast_item, args, _, _) = child.ctx.reverse_lookup(item);
                    if child.ctx.ast.lang_item_kind(ast_item) != Some(Lang::Coroutine) {
                        bail!(self, CodeDiagnostic::CoroutineReturnType);
                    }

                    Some((
                        #[allow(clippy::get_first)]
                        args.get(0).expect("incompatible signature for Coroutine"),
                        args.get(1).expect("incompatible signature for Coroutine"),
                    ))
                }
                _ => bail!(self, CodeDiagnostic::CoroutineReturnType),
            }
        } else {
            None
        };

        // We need the item to be assigned before we monomorphize the body, as the
        // function can be recursive and we need to be able to get the signature for
        // typechecking purposes.
        if signature_only {
            return Ok(());
        }

        child.return_type = Some(return_type);

        if let Some(func_body) = func.body {
            if let Some((yield_type, recv_type)) = coroutine_types {
                let mut grandchild = Self::with_replacements(
                    child.ctx,
                    child.replacements.clone(),
                    child.tentative,
                    child.current,
                    child.diag.fork(),
                );
                grandchild.local_types = child.local_types.clone();

                let inner = grandchild.ctx.ir.make_item();
                inner.assign(ir::Item::Function(ir::Function {
                    name: None,
                    attributes: [ast::Attribute::Inline(ast::Inline::DuringMono)]
                        .alloc_on(grandchild.ctx.ir),
                    args: parameters,
                    varargs: false,
                    span: func.span,
                    return_type: child.types.void(),
                    body: OnceCell::new(),
                }));
                grandchild.ctx.reverse_map.insert(inner, key);

                grandchild.return_type = Some(grandchild.types.void());
                grandchild.yield_type = Some(yield_type);
                grandchild.recv_type = Some(recv_type);

                let body = grandchild.lower_function_body(
                    func_body,
                    func.attributes
                        .contains(&ast::Attribute::Inline(ast::Inline::DuringMono)),
                    tuple_args_arg,
                )?;
                inner.get_function().unwrap().body.set(body).unwrap();

                let body = child
                    .generate_coroutine_new(parameters, yield_type, recv_type, inner, func.span)?;

                item.get_function().unwrap().body.set(body).unwrap();
            } else {
                let body = child.lower_function_body(
                    func_body,
                    func.attributes
                        .contains(&ast::Attribute::Inline(ast::Inline::DuringMono)),
                    tuple_args_arg,
                )?;
                item.get_function().unwrap().body.set(body).unwrap();
            }
        }

        Ok(())
    }

    fn generate_coroutine_new(
        &mut self,
        args: &[ir::Parameter<'ir>],
        yield_type: ir::TyP<'ir>,
        recv_type: ir::TyP<'ir>,
        item: ir::ItemP<'ir>,
        span: Option<Span>,
    ) -> Result<FuncBody<'ir>, AluminaError> {
        let tup_type = self.types.tuple(args.iter().map(|p| p.ty));
        let tup = self.exprs.tuple(
            args.iter()
                .map(|p| self.exprs.local(p.id, p.ty, span))
                .enumerate(),
            tup_type,
            span,
        );

        let call = self.call_lang_item(
            Lang::CoroutineNew,
            [self.types.named(item), tup_type, yield_type, recv_type],
            [tup],
            span,
        )?;

        assert!(self.local_defs.is_empty(), "generate_generator_new should not define any locals, so that the glue can be IR-inlined");

        Ok(FuncBody {
            local_defs: &[],
            expr: call,
        })
    }

    // Mixin expansion shouldn't really happen here, as it only touches the AST and does not
    // create any IR. However, it happens here as all the AST items have surely been populated
    // by now. In the future this should probably be a separate pass.
    fn expand_mixin(&mut self, mixin: &ast::Mixin<'ast>) -> Result<(), AluminaError> {
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
            _ => bail!(self, CodeDiagnostic::NotAProtocol),
        };

        let protocol = protocol.get_protocol();

        // TODO: Default generic args
        if protocol.placeholders.len() != generic_args.len() {
            bail!(
                self,
                CodeDiagnostic::GenericParamCountMismatch(
                    protocol.placeholders.len(),
                    generic_args.len()
                )
            );
        }

        let mut rebinder = Rebinder::new(
            self.ctx.ast,
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
                    .alloc_on(self.ctx.ast)
            };

            let body = match fun.body {
                Some(body) => rebinder.visit_expr(body)?,
                None => continue,
            };

            let new_func = self.ctx.ast.make_item();
            new_func.assign(ast::Item::Function(ast::Function {
                name: fun.name,
                attributes: fun.attributes,
                placeholders,
                return_type: rebinder.visit_ty(fun.return_type)?,
                args: fun
                    .args
                    .iter()
                    .map(|p| {
                        rebinder.visit_ty(p.ty).map(|ty| ast::Parameter {
                            id: p.id,
                            ty,
                            span: p.span,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?
                    .alloc_on(self.ctx.ast),
                body: Some(body),
                span: fun.span,
                varargs: false,
                is_local: fun.is_local,
                is_lambda: false,
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
            .set(result.alloc_on(self.ctx.ast))
            .unwrap();

        Ok(())
    }

    fn lower_function_body(
        mut self,
        expr: ast::ExprP<'ast>,
        is_ir_inline: bool,
        tuple_args_args: Option<(ir::Parameter<'ir>, &[ir::Parameter<'ir>])>,
    ) -> Result<ir::FuncBody<'ir>, AluminaError> {
        let return_type = self.return_type.unwrap();
        let body = match tuple_args_args {
            Some((tuple_param, params)) => {
                let tuple_var = self.exprs.local(tuple_param.id, tuple_param.ty, expr.span);
                self.local_defs.push(ir::LocalDef {
                    id: tuple_param.id,
                    ty: tuple_param.ty,
                });

                let stmts: Vec<_> = params
                    .iter()
                    .enumerate()
                    .map(|(idx, param)| {
                        ir::Statement::Expression(self.exprs.assign(
                            self.exprs.tuple_index(tuple_var, idx, param.ty, expr.span),
                            self.exprs.local(param.id, param.ty, expr.span),
                            expr.span,
                        ))
                    })
                    .collect();
                let actual_expr = self.lower_expr(expr, Some(return_type))?;
                self.exprs.block(stmts, actual_expr, expr.span)
            }
            None => self.lower_expr(expr, Some(return_type))?,
        };

        let body = self.try_coerce(return_type, body)?;
        if is_ir_inline {
            if self.defer_context.is_some() {
                bail!(self, CodeDiagnostic::IrInlineFlowControl);
            }
            if !self.local_defs.is_empty() {
                bail!(self, CodeDiagnostic::IrInlineLocalDefs);
            }
        };

        let body = if self.defer_context.is_some() {
            let mut statements = Vec::new();
            self.generate_defer_prologue(&mut statements);
            if let ir::ExprKind::Block(block, ret) = body.kind {
                statements.extend(block.iter().cloned());
                statements.push(ir::Statement::Expression(self.make_return(ret, ret.span)?));
            } else {
                statements.push(ir::Statement::Expression(
                    self.make_return(body, body.span)?,
                ));
            };
            self.generate_defer_epilogue(&mut statements);
            self.exprs
                .block(statements, self.exprs.unreachable(None), body.span)
        } else {
            body
        };

        let function_body = FuncBody {
            local_defs: self.local_defs.alloc_on(self.ctx.ir),
            expr: body,
        };

        Ok(function_body)
    }

    fn get_mono_key(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
        tentative: bool,
    ) -> Result<MonoKey<'ast, 'ir>, AluminaError> {
        let mut index = None;

        if tentative {
            index = self.current.map(|i| i.id)
        }

        let placeholders = match item.get() {
            ast::Item::Function(f) => {
                if f.is_local {
                    index = self.current.map(|i| i.id);
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
            .ctx
            .cycles
            .guard((item, generic_args))
            .map_err(|_| self.diag.err(CodeDiagnostic::CycleDetected))?;

        let mut args: Vec<_> = generic_args.to_vec();
        for placeholder in placeholders.iter().skip(generic_args.len()) {
            let _guard = self.diag.push_span(placeholder.span);

            match placeholder.default {
                Some(ty) => {
                    args.push(self.lower_type_unrestricted(ty)?);
                }
                None => return Ok(MonoKey::new(item, generic_args, index, tentative)),
            }
        }

        Ok(MonoKey::new(
            item,
            args.alloc_on(self.ctx.ir),
            index,
            tentative,
        ))
    }

    pub fn mono_item(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
    ) -> Result<ir::ItemP<'ir>, AluminaError> {
        self.mono_item_uncached(None, item, generic_args, false)
    }

    fn mono_item_uncached(
        &mut self,
        existing_item: Option<ItemP<'ir>>,
        item: ast::ItemP<'ast>,
        generic_args: &'ir [ir::TyP<'ir>],
        signature_only: bool,
    ) -> Result<ir::ItemP<'ir>, AluminaError> {
        // Protocol bounds checking uses signature_only to avoid infinite recursion/unpopulated items,
        // make sure other cases are appropriately handled before allowing them.
        assert!(!signature_only || matches!(item.get(), ast::Item::Function(_)));

        let key = self.get_mono_key(item, generic_args, signature_only)?;

        let item: ir::ItemP = existing_item.unwrap_or(match self.ctx.finished.entry(key.clone()) {
            // The cell may be empty at this point if we are dealing with recursive references
            // In this case, we will just return the item as is, but it will not
            // be populated until the top-level item is finished.
            Entry::Occupied(entry) => {
                if entry.get().get().is_err() {
                    match key.0.get() {
                        ast::Item::StaticOrConst(_) => {
                            bail!(self, CodeDiagnostic::RecursiveStaticInitialization)
                        }
                        _ => {}
                    }
                }
                return Ok(entry.get());
            }
            Entry::Vacant(entry) => {
                let item = self.ctx.ir.make_item();
                self.ctx.reverse_map.insert(item, key.clone());
                entry.insert(item)
            }
        });

        let old_item = std::mem::replace(&mut self.current, Some(item));
        let ret = self.mono_item_type(key, item, signature_only);
        self.current = old_item;
        ret?;

        Ok(item)
    }

    fn mono_item_type(
        &mut self,
        key: MonoKey<'ast, 'ir>,
        item: ir::ItemP<'ir>,
        signature_only: bool,
    ) -> Result<(), AluminaError> {
        let _guard = self.diag.push(Marker::Monomorphization);

        match key.0.get() {
            ast::Item::Enum(en) => {
                self.mono_enum(item, en, key.1)?;
            }
            ast::Item::Function(_) => {
                self.mono_function(item, key, signature_only)?;
            }
            ast::Item::StructLike(s) => {
                self.mono_struct(item, s, key.1)?;
            }
            ast::Item::StaticOrConst(s) => {
                self.mono_static_or_const(item, s, key.1)?;
            }
            ast::Item::Macro(_) => {
                ice!(self.diag, "macros should have been expanded by now");
            }
            ast::Item::BuiltinMacro(_) => {
                ice!(self.diag, "macros should have been expanded by now");
            }
            ast::Item::Intrinsic(_) => {
                ice!(self.diag, "intrinsics shouldn't be monomorphized");
            }
            ast::Item::Protocol(p) => {
                self.mono_protocol(item, p, key.1)?;
            }
            ast::Item::TypeDef(i) => {
                self.mono_typedef(item, i, key.1)?;
            }
        };

        Ok(())
    }

    pub fn generate_static_constructor(
        &mut self,
        alive: &HashSet<ItemP<'ir>>,
    ) -> Result<Option<ItemP<'ir>>, AluminaError> {
        self.return_type = Some(self.types.void());

        let mut statements = Vec::new();
        let mut local_defs = Vec::new();

        for (v, s) in self.ctx.static_inits.iter().filter_map(|v| match v.get() {
            Ok(ir::Item::Static(s)) if s.init.is_some() && alive.contains(v) => Some((v, s)),
            _ => None,
        }) {
            local_defs.extend(self.ctx.static_local_defs.get(v).unwrap());
            let init = s.init.unwrap();
            if init.diverges() {
                statements.push(ir::Statement::Expression(init));
                break;
            } else {
                statements.push(ir::Statement::Expression(self.exprs.assign(
                    self.exprs.static_var(v, s.ty, init.span),
                    s.init.unwrap(),
                    init.span,
                )));
            }
        }

        if statements.is_empty() {
            return Ok(None);
        }

        let body = self.exprs.block(
            statements,
            self.exprs
                .void(self.types.void(), ir::ValueType::RValue, None),
            None,
        );

        let function_body = FuncBody {
            local_defs: local_defs.alloc_on(self.ctx.ir),
            expr: body,
        };

        let item = self.ctx.ir.make_item();
        item.assign(ir::Item::Function(ir::Function {
            name: None,
            attributes: [Attribute::StaticConstructor].alloc_on(self.ctx.ir),
            args: [].alloc_on(self.ctx.ir),
            return_type: self.types.void(),
            varargs: false,
            span: None,
            body: OnceCell::from(function_body),
        }));

        Ok(Some(item))
    }

    fn mono_lang_item<I>(
        &mut self,
        kind: Lang,
        generic_args: I,
    ) -> Result<ir::ItemP<'ir>, AluminaError>
    where
        I: IntoIterator<Item = ir::TyP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let item = self.ctx.ast.lang_item(kind).with_backtrace(&self.diag)?;
        let args = self.ctx.ir.arena.alloc_slice_fill_iter(generic_args);
        self.mono_item(item, args)
    }

    fn call_lang_item<T, I>(
        &mut self,
        kind: Lang,
        generic_args: T,
        args: I,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError>
    where
        T: IntoIterator<Item = ir::TyP<'ir>>,
        T::IntoIter: ExactSizeIterator,
        I: IntoIterator<Item = ir::ExprP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let item = self.mono_lang_item(kind, generic_args)?;
        let func = self.exprs.function(item, span);
        self.call(
            func,
            args,
            item.get_function().with_backtrace(&self.diag)?.return_type,
            span,
        )
    }

    fn lang_ty<I>(&mut self, kind: Lang, generic_args: I) -> Result<ir::TyP<'ir>, AluminaError>
    where
        I: IntoIterator<Item = ir::TyP<'ir>>,
        I::IntoIter: ExactSizeIterator,
    {
        let item = self.mono_lang_item(kind, generic_args)?;
        Ok(self.types.named(item))
    }

    fn slice_of(
        &mut self,
        inner: ir::TyP<'ir>,
        is_const: bool,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        self.lang_ty(Lang::Slice, [self.types.pointer(inner, is_const)])
    }

    fn lower_type_for_value(&mut self, ty: ast::TyP<'ast>) -> Result<ir::TyP<'ir>, AluminaError> {
        let ty = self.lower_type_unrestricted(ty)?;

        // Protocols, statics, and named constants can be used as types in the context of reflection
        // or &dyn pointers, but they do not really make sense as types for actual values. Like named
        // function types, they are families of unit types, but unlike named function types, there's
        // nothing useful you can do with them.
        //
        // This is just a warning for now, but it might be worth making it an error in the future.
        //
        // Consider the following example:
        // ```
        // const X: i32 = 42;
        // let x: X; // What is the type of x?
        // ```
        if let ir::Ty::Item(item) = ty {
            match item.get() {
                Ok(
                    ir::Item::StructLike(_)
                    | ir::Item::Enum(_)
                    | ir::Item::Closure(_)
                    | ir::Item::Function(_),
                ) => {}
                Ok(ir::Item::Protocol(_)) => {
                    if !self.tentative {
                        self.diag.warn(CodeDiagnostic::ProtocolsAreSpecialMkay(
                            self.ctx.type_name(ty).unwrap(),
                        ))
                    }
                }
                Ok(ir::Item::Static(_)) => self
                    .diag
                    .warn(CodeDiagnostic::InvalidTypeForValue("statics")),
                Ok(ir::Item::Const(_)) => self
                    .diag
                    .warn(CodeDiagnostic::InvalidTypeForValue("named constants")),
                Ok(ir::Item::Alias(_)) => unreachable!("aliases should have been expanded by now"),
                Err(_) => {}
            };
        }

        Ok(ty)
    }

    // Builtin type operators
    fn try_lower_type_op(
        &mut self,
        ast_item: ast::ItemP<'ast>,
        args: &[ir::TyP<'ir>],
    ) -> Result<Option<ir::TyP<'ir>>, AluminaError> {
        macro_rules! arg_count {
            ($count:expr) => {
                if args.len() != $count {
                    bail!(self, CodeDiagnostic::InvalidTypeOperator);
                }
            };
        }

        match self.ctx.ast.lang_item_kind(ast_item) {
            Some(Lang::TypeopPointerWithMutOf) => {
                arg_count!(2);
                if let ir::Ty::Pointer(_, is_const) = args[1] {
                    return Ok(Some(self.types.pointer(args[0], *is_const)));
                }
            }
            Some(Lang::TypeopArrayWithLengthOf) => {
                arg_count!(2);
                if let ir::Ty::Array(_, len) = args[1] {
                    return Ok(Some(self.types.array(args[0], *len)));
                }
            }
            Some(Lang::TypeopGenericArgsOf) => {
                arg_count!(1);
                match args[0] {
                    ir::Ty::Item(cell) => {
                        let MonoKey(_, types, _, _) = self.ctx.reverse_lookup(cell);
                        if types.is_empty() {
                            return Ok(Some(self.types.void()));
                        } else {
                            return Ok(Some(self.types.tuple(types.iter().copied())));
                        }
                    }
                    _ => {}
                }
                bail!(self, CodeDiagnostic::InvalidTypeOperator);
            }
            Some(Lang::TypeopReplaceGenericArgsOf) => {
                arg_count!(2);
                let types = match args[1] {
                    ir::Ty::Tuple(types) => types,
                    _ => bail!(self, CodeDiagnostic::InvalidTypeOperator),
                };

                match args[0] {
                    ir::Ty::Item(cell) => {
                        let MonoKey(ast, _, _, _) = self.ctx.reverse_lookup(cell);
                        let item = self.mono_item(ast, types)?;

                        return Ok(Some(self.types.named(item)));
                    }
                    _ => {}
                }
                bail!(self, CodeDiagnostic::InvalidTypeOperator);
            }
            Some(Lang::TypeopReturnTypeOf) => {
                arg_count!(1);
                if let ir::Ty::FunctionPointer(_, ret) = args[0] {
                    return Ok(Some(*ret));
                }
                if let ir::Ty::Item(f) = args[0] {
                    match f.get().with_backtrace(&self.diag)? {
                        ir::Item::Function(f) => {
                            return Ok(Some(f.return_type));
                        }
                        ir::Item::Closure(c) => {
                            return Ok(Some(
                                c.function
                                    .get()
                                    .unwrap()
                                    .get_function()
                                    .with_backtrace(&self.diag)?
                                    .return_type,
                            ));
                        }
                        _ => {}
                    }
                }
            }
            Some(Lang::TypeopArgumentsOf) => {
                arg_count!(1);
                if let ir::Ty::FunctionPointer(args, _) = args[0] {
                    return Ok(Some(self.types.tuple(args.iter().copied())));
                }

                if let ir::Ty::Item(f) = args[0] {
                    match f.get().with_backtrace(&self.diag)? {
                        ir::Item::Function(f) => {
                            return Ok(Some(self.types.tuple(f.args.iter().map(|a| a.ty))));
                        }
                        ir::Item::Closure(c) => {
                            return Ok(Some(
                                self.types.tuple(
                                    c.function
                                        .get()
                                        .unwrap()
                                        .get_function()
                                        .with_backtrace(&self.diag)?
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
            Some(Lang::TypeopUnderlyingTypeOf) => {
                arg_count!(1);
                if let ir::Ty::Item(e) = args[0] {
                    match e.get().with_backtrace(&self.diag)? {
                        ir::Item::Enum(e) => {
                            return Ok(Some(e.underlying_ty));
                        }
                        ir::Item::Const(c) => {
                            return Ok(Some(c.ty));
                        }
                        ir::Item::Static(s) => {
                            return Ok(Some(s.ty));
                        }
                        _ => {}
                    }
                }
            }
            Some(Lang::TypeopUnderlyingFunctionOf) => {
                arg_count!(1);
                if let ir::Ty::Item(e) = args[0] {
                    match e.get().with_backtrace(&self.diag)? {
                        ir::Item::Closure(e) => {
                            return Ok(Some(
                                self.types.named(
                                    e.function
                                        .get()
                                        .ok_or(CodeDiagnostic::UnpopulatedItem)
                                        .with_backtrace(&self.diag)?,
                                ),
                            ))
                        }
                        _ => {}
                    }
                }
            }
            Some(Lang::TypeopFunctionPointerOf) => {
                arg_count!(2);
                if let ir::Ty::Tuple(tys) = args[0] {
                    return Ok(Some(self.types.function(tys.iter().copied(), args[1])));
                }
                bail!(self, CodeDiagnostic::InvalidTypeOperator);
            }
            _ => return Ok(None),
        };

        Err(self.diag.err(CodeDiagnostic::InvalidTypeOperator))
    }

    fn tuple_index_ranges(&mut self, index: ast::ExprP<'ast>) -> Result<TupleIndex, AluminaError> {
        let index = self.lower_expr(index, Some(self.types.builtin(BuiltinType::USize)))?;
        let index_val = ir::const_eval::ConstEvaluator::new(
            self.ctx.global_ctx.clone(),
            self.diag.fork(),
            self.ctx.malloc_bag.clone(),
            self.ctx.ir,
            self.local_types.iter().map(|(k, v)| (*k, *v)),
        )
        .const_eval(index)?;

        let kind = match (index.ty, self.ctx.lang_type_kind(index.ty)) {
            (ir::Ty::Builtin(BuiltinType::USize), _) => {
                if let Value::USize(idx) = index_val {
                    return Ok(TupleIndex::Single(idx));
                } else {
                    return Err(mismatch!(
                        self,
                        self.types.builtin(BuiltinType::USize),
                        index.ty
                    ));
                }
            }
            (_, Some(LangKind::Range(ir::Ty::Builtin(BuiltinType::USize), kind))) => kind,
            _ => {
                return Err(mismatch!(
                    self,
                    self.types.builtin(BuiltinType::USize),
                    index.ty
                ))
            }
        };

        // This extracts the fields from the Range struct. This should be a lang item eventually
        // but it's a lot of different cases to handle.
        let fields = {
            let Value::Struct(fields) = index_val else {
                return Err(mismatch!(
                    self,
                    self.types.builtin(BuiltinType::USize),
                    index.ty
                ));
            };
            let mut fields = fields.to_vec();
            // TODO: This is a hack, we rely on the fact that the fields ids are set in order of definition
            fields.sort_by(|(a, _), (b, _)| a.cmp(b));
            fields
        };

        match (kind, &fields[..]) {
            (RangeKind::Range, [(_, Value::USize(lower)), (_, Value::USize(upper)), ..]) => Ok(
                TupleIndex::Range(Bound::Included(*lower), Bound::Excluded(*upper)),
            ),
            (RangeKind::RangeFrom, [(_, Value::USize(lower), ..)]) => {
                Ok(TupleIndex::Range(Bound::Included(*lower), Bound::Unbounded))
            }
            (RangeKind::RangeTo, [(_, Value::USize(upper), ..)]) => {
                Ok(TupleIndex::Range(Bound::Unbounded, Bound::Excluded(*upper)))
            }
            (RangeKind::RangeFull, []) => Ok(TupleIndex::Range(Bound::Unbounded, Bound::Unbounded)),
            (
                RangeKind::RangeInclusive,
                [(_, Value::USize(lower)), (_, Value::USize(upper)), ..],
            ) => Ok(TupleIndex::Range(
                Bound::Included(*lower),
                Bound::Included(*upper),
            )),
            (RangeKind::RangeToInclusive, [(_, Value::USize(upper), ..)]) => {
                Ok(TupleIndex::Range(Bound::Unbounded, Bound::Included(*upper)))
            }
            _ => Err(mismatch!(
                self,
                self.types.builtin(BuiltinType::USize),
                index.ty
            )),
        }
    }

    fn lower_type_unrestricted(
        &mut self,
        ty: ast::TyP<'ast>,
    ) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *ty {
            ast::Ty::Tag(_, inner) => self.lower_type_unrestricted(inner)?,
            ast::Ty::Builtin(kind) => self.types.builtin(kind),
            ast::Ty::Array(inner, len) => {
                let inner = self.lower_type_for_value(inner)?;
                let mut child = self.fork(false);
                let len_expr =
                    child.lower_expr(len, Some(child.types.builtin(BuiltinType::USize)))?;
                let len = ir::const_eval::ConstEvaluator::new(
                    child.ctx.global_ctx.clone(),
                    child.diag.fork(),
                    child.ctx.malloc_bag.clone(),
                    child.ctx.ir,
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
            ast::Ty::Deref(inner) => {
                let inner = self.lower_type_for_value(inner)?;
                match inner {
                    ir::Ty::Pointer(inner, _) => inner,
                    _ => bail!(
                        self,
                        CodeDiagnostic::NotAPointer(self.ctx.type_name(inner).unwrap())
                    ),
                }
            }
            ast::Ty::TupleIndex(inner, idx) => {
                let inner = self.lower_type_for_value(inner)?;
                let ir::Ty::Tuple(tys) = inner else {
                    bail!(
                        self,
                        CodeDiagnostic::NotATuple(self.ctx.type_name(inner).unwrap())
                    );
                };

                match self.tuple_index_ranges(idx)? {
                    TupleIndex::Single(idx) => tys
                        .get(idx)
                        .copied()
                        .ok_or_else(|| self.diag.err(CodeDiagnostic::TupleIndexOutOfBounds))?,
                    TupleIndex::Range(start, end) => {
                        let tys = tys
                            .get((start, end))
                            .ok_or_else(|| self.diag.err(CodeDiagnostic::TupleIndexOutOfBounds))?;
                        self.types.tuple(tys.iter().copied())
                    }
                }
            }
            ast::Ty::FunctionPointer(args, ret) | ast::Ty::FunctionProtocol(args, ret) => {
                let mut args_ir = Vec::new();
                for item in args.iter() {
                    match item {
                        ast::Ty::EtCetera(inner) => match self.lower_type_for_value(inner)? {
                            ir::Ty::Tuple(tys) => args_ir.extend(tys.iter().copied()),
                            _ => bail!(self, CodeDiagnostic::EtCeteraOnNonTuple),
                        },
                        _ => args_ir.push(self.lower_type_for_value(item)?),
                    }
                }
                let ret = self.lower_type_for_value(ret)?;

                match ty {
                    ast::Ty::FunctionPointer(..) => self.types.function(args_ir, ret),
                    ast::Ty::FunctionProtocol(..) => {
                        self.lang_ty(Lang::ProtoCallable, [self.types.tuple(args_ir), ret])?
                    }
                    _ => unreachable!(),
                }
            }
            ast::Ty::Tuple(items) => {
                let mut items_ir = Vec::new();
                for item in items.iter() {
                    match item {
                        ast::Ty::EtCetera(inner) => match self.lower_type_for_value(inner)? {
                            ir::Ty::Tuple(tys) => items_ir.extend(tys.iter().copied()),
                            _ => bail!(self, CodeDiagnostic::EtCeteraOnNonTuple),
                        },
                        _ => items_ir.push(self.lower_type_for_value(item)?),
                    }
                }

                self.types.tuple(items_ir)
            }
            ast::Ty::Placeholder(id) => self.replacements.get(&id).copied().ok_or_else(|| {
                self.diag.err(CodeDiagnostic::InternalError(
                    "unbound placeholder".to_string(),
                    Backtrace::capture().into(),
                ))
            })?,
            ast::Ty::Item(item) => match self.ctx.ast.lang_item_kind(item) {
                Some(Lang::ImplBuiltin(kind)) => self.types.builtin(kind),
                Some(Lang::ImplArray | Lang::ImplTuple) => {
                    bail!(self, CodeDiagnostic::BuiltinTypesAreSpecialMkay);
                }
                _ => {
                    let item = self.mono_item(item, &[])?;
                    if let Some(ty) = item.get_alias() {
                        return Ok(ty);
                    }

                    self.types.named(item)
                }
            },
            ast::Ty::Generic(inner, args) => {
                let item = match inner {
                    ast::Ty::Item(item) => item,
                    ast::Ty::Defered(spec) => self.resolve_defered_func(spec)?,
                    _ => ice!(self.diag, "unsupported generic type"),
                };

                let args = args
                    .iter()
                    .map(|arg| self.lower_type_unrestricted(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ctx.ir);

                if let Some(ty) = self.try_lower_type_op(item, args)? {
                    return Ok(ty);
                }

                let ir_item = self.mono_item(item, args)?;
                if let Some(ty) = ir_item.get_alias() {
                    return Ok(ty);
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
                let ir_item = self.mono_item(item, &[])?;
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
                                protocol_item.get().with_backtrace(&self.diag)?,
                                ir::Item::Protocol(_)
                            ) =>
                        {
                            let MonoKey(ast_item, _, _, _) = self.ctx.reverse_lookup(protocol_item);

                            if let Some(p) = self.ctx.ast.lang_item_kind(ast_item) {
                                if p.is_builtin_protocol() {
                                    bail!(self, CodeDiagnostic::BuiltinProtocolDyn);
                                }
                            }

                            protocol_items.push(*protocol_item)
                        }
                        _ => bail!(self, CodeDiagnostic::NonProtocolDyn),
                    };
                }

                let key = protocols.alloc_on(self.ctx.ir);
                let key_ty = self.ctx.ir.intern_type(ir::Ty::Tuple(key));

                let ptr_type = self.types.pointer(self.types.void(), is_const);
                self.create_vtable_layout(key)?;
                self.lang_ty(Lang::Dyn, [key_ty, ptr_type])?
            }
            ast::Ty::TypeOf(inner) => {
                let mut child = self.fork(false);
                let expr = child.lower_expr(inner, None)?;
                expr.ty
            }
            ast::Ty::When(cond, then, els) => {
                // Do not move outside the branch, this must evaluate lazily as the non-matching
                // branch may contain a compile error.
                if self.static_cond_matches(cond)? {
                    self.lower_type_unrestricted(then)?
                } else {
                    self.lower_type_unrestricted(els)?
                }
            }
            ast::Ty::EtCetera(_) => ice!(self.diag, "et cetera types should have been expanded"),
        };

        Ok(result)
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
            ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag) {
                Ok(ir::Item::Protocol(_)) => false,
                _ => self
                    .ctx
                    .reverse_lookup(item)
                    .1
                    .iter()
                    .any(|ty| self.contains_type(ty, needle)),
            },
            _ => false,
        }
    }

    fn create_vtable_layout(&mut self, protocols: &'ir [ir::TyP<'ir>]) -> Result<(), AluminaError> {
        if self.ctx.vtable_layouts.contains_key(protocols) {
            return Ok(());
        }

        let dyn_self = self.lang_ty(Lang::DynSelf, [])?;
        let mut vtable_methods = Vec::new();

        for protocol_ty in protocols {
            let protocol_item = match protocol_ty {
                ir::Ty::Item(item) => item,
                _ => unreachable!(),
            };

            let protocol = protocol_item.get_protocol().with_backtrace(&self.diag)?;
            for proto_fun in protocol.methods {
                macro_rules! nope {
                    () => {
                        bail!(
                            self,
                            CodeDiagnostic::NonDynnableFunction(proto_fun.name.to_string())
                        )
                    };
                }

                if self.contains_type(proto_fun.return_type, dyn_self) {
                    nope!()
                }

                let args = match proto_fun.arg_types {
                    [ir::Ty::Pointer(ty, is_const), rest @ ..] => {
                        if *ty != dyn_self || rest.iter().any(|ty| self.contains_type(ty, dyn_self))
                        {
                            nope!()
                        }

                        std::iter::once(self.types.pointer(self.types.void(), *is_const))
                            .chain(rest.iter().copied())
                            .collect::<Vec<_>>()
                            .alloc_on(self.ctx.ir)
                    }
                    _ => nope!(),
                };

                vtable_methods.push(ir::ProtocolFunction {
                    name: proto_fun.name,
                    arg_types: args,
                    return_type: proto_fun.return_type,
                });
            }
        }

        self.ctx.vtable_layouts.insert(
            protocols,
            ir::VtableLayout {
                methods: vtable_methods.alloc_on(self.ctx.ir),
            },
        );

        Ok(())
    }

    fn raise_type(&mut self, ty: ir::TyP<'ir>) -> Result<ast::TyP<'ast>, AluminaError> {
        let result = match ty {
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
                    .alloc_on(self.ctx.ast),
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

                ast::Ty::FunctionPointer(args.alloc_on(self.ctx.ast), ret)
            }
            ir::Ty::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|arg| self.raise_type(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                ast::Ty::Tuple(items.alloc_on(self.ctx.ast))
            }
            ir::Ty::Item(item) => {
                let item = self.ctx.reverse_lookup(item);
                let base = match ty {
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

                    ast::Ty::Generic(self.ctx.ast.intern_type(base), args.alloc_on(self.ctx.ast))
                }
            }
        };

        Ok(self.ctx.ast.intern_type(result))
    }

    fn struct_field_map(
        &mut self,
        item: ir::ItemP<'ir>,
    ) -> Result<Rc<HashMap<&'ast str, &'ir ir::Field<'ir>>>, AluminaError> {
        if let Some(map) = self.ctx.caches.struct_field_maps.get(&item) {
            return Ok(map.clone());
        }

        let map = Rc::new(self.struct_field_map_uncached(item)?);

        self.ctx.caches.struct_field_maps.insert(item, map.clone());

        Ok(map)
    }

    fn struct_field_map_uncached(
        &mut self,
        item: ir::ItemP<'ir>,
    ) -> Result<HashMap<&'ast str, &'ir ir::Field<'ir>>, AluminaError> {
        let MonoKey(ast_item, _, _, _) = self.ctx.reverse_lookup(item);
        let ir_struct = item.get_struct_like().with_backtrace(&self.diag)?;
        let ast_struct = ast_item.get_struct_like();

        let res = ast_struct
            .fields
            .iter()
            .map(|ast_f| {
                ir_struct
                    .fields
                    .iter()
                    .find(|ir_f| self.ctx.map_id(ast_f.id) == ir_f.id)
                    .map(|f| (ast_f.name, f))
                    .unwrap()
            })
            .collect();

        Ok(res)
    }

    fn associated_fns(
        &mut self,
        ty: ir::TyP<'ir>,
    ) -> Result<Rc<HashMap<&'ast str, ast::ItemP<'ast>>>, AluminaError> {
        if let Some(c) = self.ctx.caches.associated_fns.get(&ty) {
            return Ok(c.clone());
        }

        let raised = self.raise_type(ty)?;
        let associated_fns = self.associated_fns_for_ast(raised)?;

        self.ctx
            .caches
            .associated_fns
            .insert(ty, associated_fns.clone());

        Ok(associated_fns)
    }

    fn associated_fns_for_ast(
        &mut self,
        ty: ast::TyP<'ast>,
    ) -> Result<Rc<HashMap<&'ast str, ast::ItemP<'ast>>>, AluminaError> {
        if let Some(c) = self.ctx.caches.associated_fns_ast.get(&ty) {
            return Ok(c.clone());
        }

        let associated_fns = Rc::new(self.associated_fns_uncached(ty)?);
        self.ctx
            .caches
            .associated_fns_ast
            .insert(ty, associated_fns.clone());

        Ok(associated_fns)
    }

    fn associated_fns_uncached(
        &mut self,
        ty: ast::TyP<'ast>,
    ) -> Result<HashMap<&'ast str, ast::ItemP<'ast>>, AluminaError> {
        let mut associated_fns = HashMap::default();

        let item = match ty {
            ast::Ty::Builtin(kind) => self
                .ctx
                .ast
                .lang_item(Lang::ImplBuiltin(*kind))
                .with_backtrace(&self.diag)?,
            ast::Ty::Array(_, _) => self
                .ctx
                .ast
                .lang_item(Lang::ImplArray)
                .with_backtrace(&self.diag)?,
            ast::Ty::Tuple(_) => self
                .ctx
                .ast
                .lang_item(Lang::ImplTuple)
                .with_backtrace(&self.diag)?,
            ast::Ty::Defered(..) | ast::Ty::FunctionPointer(..) => self
                .ctx
                .ast
                .lang_item(Lang::ImplCallable)
                .with_backtrace(&self.diag)?,
            ast::Ty::Item(item) if matches!(item.get(), ast::Item::Function(_)) => self
                .ctx
                .ast
                .lang_item(Lang::ImplCallable)
                .with_backtrace(&self.diag)?,

            ast::Ty::Item(item) => item,
            ast::Ty::Generic(inner, _) => return self.associated_fns_uncached(inner),
            _ => return Ok(associated_fns),
        };

        let (fns, mixins) = match item.get() {
            ast::Item::StructLike(s) => (s.associated_fns, s.mixins),
            ast::Item::Enum(e) => (e.associated_fns, e.mixins),
            _ => return Ok(associated_fns),
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

    fn fork<'b>(&'b mut self, tentative: bool) -> Mono<'b, 'ast, 'ir> {
        let ir = self.ctx.ir;

        // this should be some CoW thing, cloning everything here is excessive
        Mono {
            ctx: self.ctx,
            replacements: self.replacements.clone(),
            local_types: self.local_types.clone(),
            exprs: ExpressionBuilder::new(ir),
            types: TypeBuilder::new(ir),
            return_type: self.return_type,
            yield_type: self.yield_type,
            recv_type: self.recv_type,
            loop_contexts: self.loop_contexts.clone(),
            local_defs: self.local_defs.clone(),
            local_type_hints: self.local_type_hints.clone(),
            defer_context: self.defer_context.clone(),
            const_replacements: self.const_replacements.clone(),
            current: self.current,
            tentative,
            diag: self.diag.fork(),
        }
    }

    fn try_coerce(
        &mut self,
        lhs_ty: ir::TyP<'ir>,
        rhs: ir::ExprP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let _guard = self.diag.push_span(rhs.span);

        if lhs_ty.assignable_from(rhs.ty) {
            return Ok(rhs);
        }

        match (lhs_ty, rhs.ty) {
            (ir::Ty::FunctionPointer(args, ret), ir::Ty::Item(item)) => {
                match item.get().with_backtrace(&self.diag)? {
                    ir::Item::Function(fun) => {
                        if fun.args.len() != args.len() {
                            return Err(mismatch!(self, lhs_ty, rhs.ty));
                        }
                        // There is no co- and contra-variance, argument and return types must match
                        // exactly.
                        if fun.return_type != *ret {
                            return Err(mismatch!(self, lhs_ty, rhs.ty));
                        }
                        for (a, b) in fun.args.iter().zip(args.iter()) {
                            if a.ty != *b {
                                return Err(mismatch!(self, lhs_ty, rhs.ty));
                            }
                        }

                        // Named functions directly coerce into function pointers, cast it to avoid
                        // ZST elision issues later on.
                        let result = self.exprs.cast(rhs, lhs_ty, rhs.span);

                        return Ok(result.alloc_on(self.ctx.ir));
                    }
                    ir::Item::Closure(_) => bail!(self, CodeDiagnostic::ClosuresAreNotFns),
                    _ => {}
                }
            }
            _ => {}
        };

        let lhs_lang = self.ctx.lang_type_kind(lhs_ty);
        let rhs_lang = self.ctx.lang_type_kind(rhs.ty);

        match (&lhs_lang, rhs_lang) {
            // &mut [T] -> &[T]
            (Some(LangKind::Slice(t1_ptr)), Some(LangKind::Slice(t2_ptr))) => {
                match (t1_ptr, t2_ptr) {
                    (ir::Ty::Pointer(t1, true), ir::Ty::Pointer(t2, _)) if t1 == t2 => {
                        return self.call_lang_item(Lang::SliceConstCoerce, [*t1], [rhs], rhs.span);
                    }
                    _ => {}
                }
            }
            // &mut dyn Proto -> &dyn Proto
            (Some(LangKind::Dyn(t1_proto, t1_ptr)), Some(LangKind::Dyn(t2_proto, t2_ptr)))
                if *t1_proto == t2_proto =>
            {
                match (t1_ptr, t2_ptr) {
                    (ir::Ty::Pointer(t1, true), ir::Ty::Pointer(t2, _)) if t1 == t2 => {
                        return self.call_lang_item(
                            Lang::DynConstCoerce,
                            [*t1_proto],
                            [rhs],
                            rhs.span,
                        );
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        // &[T; size] -> &[T]
        // &mut [T; size] -> &[T]
        // &mut [T; size] -> &mut [T]
        // This coercion should be a lang function when we support const usize generics
        match (&lhs_lang, rhs.ty) {
            (Some(LangKind::Slice(t1_ptr)), ir::Ty::Pointer(ir::Ty::Array(t2, size), t2_const)) => {
                match t1_ptr {
                    ir::Ty::Pointer(t1, t1_const) if *t1 == *t2 && (!t2_const || *t1_const) => {
                        let size_lit = self.exprs.literal(
                            Value::USize(*size),
                            self.types.builtin(BuiltinType::USize),
                            rhs.span,
                        );
                        let data = self.exprs.r#ref(
                            self.exprs
                                .const_index(self.exprs.deref(rhs, rhs.span), 0, rhs.span),
                            rhs.span,
                        );
                        return self.call_lang_item(
                            Lang::SliceNew,
                            [*t1_ptr],
                            [data, size_lit],
                            rhs.span,
                        );
                    }
                    _ => {}
                }
            }
            (Some(LangKind::Dyn(t1_proto, t1_ptr)), ir::Ty::Pointer(t2, t2_const)) => {
                match t1_ptr {
                    ir::Ty::Pointer(_, t1_const) if !t2_const || *t1_const => {
                        let ty: &ir::Ty<'_> = self.types.pointer(t2, *t1_const);
                        return self.call_lang_item(Lang::DynNew, [*t1_proto, ty], [rhs], rhs.span);
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        Err(mismatch!(self, lhs_ty, rhs.ty))
    }

    fn try_resolve_function(
        &mut self,
        item: ast::ItemP<'ast>,
        generic_args: Option<&[ast::TyP<'ast>]>,
        self_expr: Option<ir::ExprP<'ir>>,
        tentative_args: Option<&[ast::ExprP<'ast>]>,
        return_type_hint: Option<ir::TyP<'ir>>,
        args_hint: Option<&[ir::TyP<'ir>]>,
    ) -> Result<ir::ItemP<'ir>, AluminaError> {
        let fun = item.get_function();

        // If the generic args are provided, we don't need to infer them
        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|ty| self.lower_type_unrestricted(ty))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.ctx.ir);

            return self.mono_item(item, generic_args);
        }

        if fun.placeholders.is_empty() {
            return self.mono_item(item, &[]);
        }

        // If the function is generic but no args are provided, we can try to infer the args
        // based on the types of the function's parameters and provided arguments in matching
        // positions and the return type with type_hint Since we have not yet monomorphized the
        // arguments, we do so tentatively in a fresh monomorphizer without the type_hint.
        // If the monomorphization of an argument fails for whatever reason, we skip that arg,
        // but do not rethrow the error as the resolution might still succeed.

        let mut infer_pairs: Vec<(ast::TyP<'ast>, ir::TyP<'ir>)> = Vec::new();

        let mut tentative_errors = Vec::new();
        let self_count = self_expr.iter().count();

        let arg_types = if let Some(tentative_args) = tentative_args {
            let mut child = self.fork(true);
            let arg_types = tentative_args
                .iter()
                .map(|e| match child.lower_expr(e, None) {
                    Ok(e) => Ok(Some(e.ty)),
                    Err(AluminaError::CodeErrors(errors)) => {
                        tentative_errors.extend(
                            errors
                                .into_iter()
                                .filter(|f| !matches!(f.kind, CodeDiagnostic::TypeHintRequired)),
                        );
                        Ok(None)
                    }
                    Err(e) => Err(e),
                })
                .collect::<Result<Vec<_>, _>>()?;

            if !tentative_errors.is_empty() {
                return Err(AluminaError::CodeErrors(tentative_errors));
            }

            Some(arg_types)
        } else {
            args_hint.map(|args_hint| args_hint.iter().copied().map(Some).collect())
        };

        let mut self_slot = fun.args.first().zip(self_expr).map(|(a, e)| (a.ty, e.ty));
        if let Some(mut arg_types) = arg_types {
            if fun.attributes.contains(&ast::Attribute::TupleCall) {
                // If the function argument is explicitely a tuple in AST (which is not terribly useful), we can do better
                // than if it is provided as e.g. generic argument.
                if let Some(ast::Ty::Tuple(inner)) = fun.args.first().map(|a| a.ty) {
                    if inner.len() != self_count + arg_types.len() {
                        bail!(
                            self,
                            if inner.len() < self_count {
                                CodeDiagnostic::NotAMethod
                            } else {
                                CodeDiagnostic::ParamCountMismatch(
                                    inner.len() - self_count,
                                    arg_types.len(),
                                )
                            }
                        );
                    }

                    self_slot = self_expr.map(|e| (inner[0], e.ty));
                    infer_pairs.extend(
                        inner
                            .iter()
                            .skip(self_count)
                            .zip(arg_types)
                            .filter_map(|(p, e)| Some(*p).zip(e)),
                    );
                } else {
                    self_slot = None;
                    if let Some(self_arg) = self_expr {
                        // This will probably not work correctly with autoref, but OTOH, don't put
                        // #[tuple_args] on methods.
                        arg_types.insert(0, Some(self_arg.ty));
                    }

                    if let Some(arg_types) = arg_types.into_iter().collect::<Option<Vec<_>>>() {
                        infer_pairs.push((fun.args[0].ty, self.types.tuple(arg_types)));
                    }
                }
            } else {
                if fun.args.len() != arg_types.len() + self_count {
                    bail!(
                        self,
                        if fun.args.len() < self_count {
                            CodeDiagnostic::NotAMethod
                        } else {
                            CodeDiagnostic::ParamCountMismatch(
                                fun.args.len() - self_count,
                                arg_types.len(),
                            )
                        }
                    );
                }
                self_slot = self_expr.map(|e| (fun.args[0].ty, e.ty));
                infer_pairs.extend(
                    fun.args
                        .iter()
                        .skip(self_count)
                        .zip(arg_types)
                        .filter_map(|(p, e)| Some(p.ty).zip(e)),
                );
            }
        }

        if let Some(return_type_hint) = return_type_hint {
            infer_pairs.push((fun.return_type, return_type_hint));
        }

        let mut type_inferer = TypeInferer::new(
            self.ctx.ast,
            self.ctx.ir,
            self.ctx,
            fun.placeholders.to_vec(),
        );

        match type_inferer.try_infer(self_slot, infer_pairs.clone()) {
            Some(generic_args) => self.mono_item(item, generic_args.alloc_on(self.ctx.ir)),
            None => Err(self.diag.err(CodeDiagnostic::TypeHintRequired)),
        }
    }

    fn try_resolve_struct(
        &mut self,
        ty: ast::TyP<'ast>,
        initializers: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ItemP<'ir>, AluminaError> {
        let (item, generic_args) = match ty {
            ast::Ty::Item(item) => (*item, None),
            ast::Ty::Generic(ast::Ty::Item(item), generic_args) => (*item, Some(*generic_args)),
            _ => {
                let lowered = self.lower_type_for_value(ty)?;
                match lowered {
                    ir::Ty::Item(item) if item.is_struct_like() => return Ok(item),
                    _ => bail!(self, CodeDiagnostic::StructLikeExpectedHere),
                }
            }
        };

        let r#struct = match item.get() {
            ast::Item::StructLike(s) => s,
            _ => bail!(self, CodeDiagnostic::StructLikeExpectedHere),
        };

        if let Some(generic_args) = generic_args {
            let generic_args = generic_args
                .iter()
                .map(|ty| self.lower_type_unrestricted(ty))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.ctx.ir);

            return self.mono_item(item, generic_args);
        }

        // If the struct is not generic, we don't need to infer the args
        if r#struct.placeholders.is_empty() {
            return self.mono_item(item, &[]);
        }

        // If the parent of this expression expects a specific struct, we trust that this is
        // in fact the correct monomorphization.
        if let Some(ir::Ty::Item(hint_item)) = type_hint {
            let MonoKey(ast_hint_item, _, _, _) = self.ctx.reverse_lookup(hint_item);
            if item == ast_hint_item {
                return Ok(hint_item);
            }
        }

        // See notes in try_resolve_function. Same thing, but for struct fields (we match by name instead of position).

        let mut tentative_errors = Vec::new();
        let mut child = self.fork(true);
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
                Ok(e) => Some(Ok((p.ty, e.ty))),
                Err(AluminaError::CodeErrors(errors)) => {
                    tentative_errors.extend(
                        errors
                            .into_iter()
                            .filter(|f| !matches!(f.kind, CodeDiagnostic::TypeHintRequired)),
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
            self.ctx.ast,
            self.ctx.ir,
            self.ctx,
            r#struct.placeholders.to_vec(),
        );
        let infer_result = type_inferer.try_infer(None, pairs);

        match infer_result {
            Some(generic_args) => self.mono_item(item, generic_args.alloc_on(self.ctx.ir)),
            None => Err(self.diag.err(CodeDiagnostic::TypeHintRequired)),
        }
    }

    fn make_local(&mut self, ty: ir::TyP<'ir>, span: Option<Span>) -> ir::ExprP<'ir> {
        let id = self.ctx.ir.make_id();
        self.local_defs.push(ir::LocalDef { id, ty });
        self.local_types.insert(id, ty);

        self.exprs.local(id, ty, span)
    }

    /// Take reference of anything, promoting the lifetime if it is a rvalue.
    fn r#ref(&mut self, expr: ir::ExprP<'ir>, span: Option<Span>) -> ir::ExprP<'ir> {
        if matches!(expr.value_type, ValueType::LValue) {
            return self.exprs.r#ref(expr, span);
        }

        let local = self.make_local(expr.ty, span);
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
        let mut a_ty = expr.ty;
        while let ir::Ty::Pointer(inner, _) = a_ty {
            a += 1;
            a_ty = inner;
        }

        let mut b: isize = 0;
        let mut b_ty = target;
        while let ir::Ty::Pointer(inner, _) = b_ty {
            b += 1;
            b_ty = *inner;
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
    ) -> Result<ir::TyP<'ir>, CodeDiagnostic> {
        use ast::BinOp::*;
        use ir::Ty::*;

        let result_ty = match (lhs.ty, op, rhs.ty) {
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
            (Item(l), Eq | Neq, Item(r)) if l == r && matches!(l.get()?, ir::Item::Enum(_)) => {
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

            // Function pointer equality comparison only
            (FunctionPointer(l_a, l_b), Eq | Neq, FunctionPointer(r_a, r_b))
                if *l_a == *r_a && l_b == r_b =>
            {
                self.types.builtin(BuiltinType::Bool)
            }

            // Bit shifts
            (Builtin(l), LShift | RShift, Builtin(r)) if l.is_integer() && r.is_integer() => lhs.ty,

            // Pointer arithmetic
            (Pointer(l, l_const), Minus, Pointer(r, r_const)) if l == r && l_const == r_const => {
                if l.is_zero_sized() {
                    return Err(CodeDiagnostic::ZstPointerDifference);
                } else {
                    self.types.builtin(BuiltinType::ISize)
                }
            }
            (Pointer(l, _), Plus | Minus, Builtin(BuiltinType::ISize | BuiltinType::USize)) => {
                if l.is_zero_sized() {
                    return Err(CodeDiagnostic::ZstPointerOffset);
                } else {
                    lhs.ty
                }
            }

            _ => {
                return Err(CodeDiagnostic::InvalidBinOp(
                    op,
                    self.ctx.type_name(lhs.ty).unwrap(),
                    self.ctx.type_name(rhs.ty).unwrap(),
                ))
            }
        };

        Ok(result_ty)
    }

    fn lower_stmt(
        &mut self,
        stmt: &ast::Statement<'ast>,
    ) -> Result<Option<ir::Statement<'ir>>, AluminaError> {
        let result = match &stmt.kind {
            ast::StatementKind::Expression(expr) => {
                let expr = self.lower_expr(expr, None)?;

                let must_use = match expr.ty {
                    ir::Ty::Item(item) => item
                        .attributes()
                        .contains(&ast::Attribute::Diagnostic(ast::Diagnostic::MustUse)),
                    _ => false,
                };

                if must_use && !self.tentative {
                    let type_name = self.ctx.type_name(expr.ty)?;
                    self.diag.warn(CodeDiagnostic::UnusedMustUse(type_name))
                }

                if expr.pure() && !expr.is_void() {
                    self.diag.warn(CodeDiagnostic::PureStatement);
                }

                Some(ir::Statement::Expression(expr))
            }
            ast::StatementKind::LetDeclaration(decl) => {
                let id = self.ctx.map_id(decl.id);
                let type_hint = decl.ty.map(|t| self.lower_type_for_value(t)).transpose()?;
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
                    (None, None) => bail!(self, CodeDiagnostic::TypeHintRequired),
                    (Some(ty), None) => {
                        self.local_types.insert(id, ty);
                        self.local_defs.push(ir::LocalDef { id, ty });
                        None
                    }
                    (None, Some(init)) => {
                        self.local_types.insert(id, init.ty);
                        self.local_defs.push(ir::LocalDef { id, ty: init.ty });

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
                        self.local_defs.push(ir::LocalDef { id, ty });

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
        let mut local_id: Option<ir::Id> = None;
        if let ast::ExprKind::Local(id) = ret.kind {
            // This is a hack so the following works:
            // let a: Ty = { let b = a; ...; b };
            let id = self.ctx.map_id(id);
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
        let statements: Vec<_> = statements
            .iter()
            .map(|stmt| {
                let _guard = self.diag.push_span(stmt.span);
                self.lower_stmt(stmt)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let ret = self.lower_expr(ret, type_hint)?;

        let mut never_return = false;

        Ok(self.exprs.block(
            statements.into_iter().flat_map(|s| {
                if let Some(ir::Statement::Expression(expr)) = s {
                    if never_return {
                        let _guard = self.diag.push_span(expr.span);
                        self.diag.warn(CodeDiagnostic::DeadCode);
                    } else if expr.diverges() {
                        never_return = true
                    }
                }

                s
            }),
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
                let type_name = self.ctx.type_name(ty)?;

                Err(self
                    .diag
                    .err(CodeDiagnostic::IntegerOutOfRange(value, type_name)))
            }
        }
    }

    fn lower_lit(
        &mut self,
        ret: &ast::Lit<'_>,
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

                match ty {
                    ir::Ty::Builtin(BuiltinType::F32) => {
                        let v = v.parse().or_else(|_| {
                            let type_name = self.ctx.type_name(ty)?;
                            Err(self
                                .diag
                                .err(CodeDiagnostic::FloatOutOfRange(v.to_string(), type_name)))
                        })?;

                        self.exprs.literal(Value::F32(v), ty, ast_span)
                    }
                    ir::Ty::Builtin(BuiltinType::F64) => {
                        let v = v.parse().or_else(|_| {
                            let type_name = self.ctx.type_name(ty)?;
                            Err(self
                                .diag
                                .err(CodeDiagnostic::FloatOutOfRange(v.to_string(), type_name)))
                        })?;

                        self.exprs.literal(Value::F64(v), ty, ast_span)
                    }
                    _ => ice!(self.diag, "unexpected type for the float literal"),
                }
            }
            ast::Lit::Str(v) => self.string_of(v, ast_span)?,
        };

        Ok(result)
    }

    fn lower_deref(
        &mut self,
        inner: ast::ExprP<'ast>,
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

        Ok(result.alloc_on(self.ctx.ir))
    }

    fn lower_ref(
        &mut self,
        inner: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let type_hint = match type_hint {
            Some(ir::Ty::Pointer(inner, _)) => Some(*inner),
            Some(hint) => {
                if let Some(LangKind::Slice(ir::Ty::Pointer(ty, _))) = self.ctx.lang_type_kind(hint)
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
        id: ast::Id,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let id = self.ctx.map_id(id);
        let ty = self
            .local_types
            .get(&id)
            .copied()
            .ok_or_else(|| self.diag.err(CodeDiagnostic::LocalWithUnknownType))?;

        if let Some(replacment) = self.const_replacements.get(&id) {
            Ok(self.exprs.literal(*replacment, ty, ast_span))
        } else {
            Ok(self.exprs.local(id, ty, ast_span))
        }
    }

    fn lower_bound_param(
        &mut self,
        self_arg: ast::Id,
        field_id: ast::Id,
        bound_type: BoundItemType,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let self_arg = self.ctx.map_id(self_arg);
        let field_id = self.ctx.map_id(field_id);

        let ty = self
            .local_types
            .get(&self_arg)
            .copied()
            .ok_or_else(|| self.diag.err(CodeDiagnostic::LocalWithUnknownType))?;

        match ty.canonical_type() {
            ir::Ty::Item(item) => {
                let closure = item.get_closure().with_backtrace(&self.diag)?;
                let field_ty = closure
                    .data
                    .fields
                    .iter()
                    .find(|f| f.id == field_id)
                    .unwrap()
                    .ty;

                let mut obj = self.exprs.local(self_arg, ty, ast_span);
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
                .map(|ty| self.lower_type_unrestricted(ty))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.ctx.ir);

            self.mono_item(item, generic_args)?
        } else {
            self.mono_item(item, &[])?
        };

        let item = item_cell.get_static().with_backtrace(&self.diag)?;
        Ok(self.exprs.static_var(item_cell, item.ty, ast_span))
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
                .map(|ty| self.lower_type_unrestricted(ty))
                .collect::<Result<Vec<_>, _>>()?
                .alloc_on(self.ctx.ir);

            self.mono_item(item, generic_args)?
        } else {
            self.mono_item(item, &[])?
        };
        let r#const = item_cell.get_const().with_backtrace(&self.diag)?;
        Ok(self.exprs.const_var(item_cell, r#const.ty, ast_span))
    }

    fn lower_unary(
        &mut self,
        op: ast::UnOp,
        inner: ast::ExprP<'ast>,
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
                bail!(
                    self,
                    CodeDiagnostic::InvalidUnOp(op, self.ctx.type_name(inner.ty).unwrap())
                );
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
        let ty = lhs.ty;

        let rhs = self.try_coerce(lhs.ty, rhs)?;
        let lhs = self.r#ref(lhs, ast_span);
        let rhs = self.r#ref(rhs, ast_span);

        self.call_lang_item(Lang::Operator(op), [ty], [lhs, rhs], ast_span)
    }

    fn lower_binary(
        &mut self,
        op: ast::BinOp,
        lhs: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
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
            Ok(result_ty) => Ok(self.exprs.binary(op, lhs, rhs, result_ty, ast_span)),
            // Operator overloading
            Err(original_diag @ CodeDiagnostic::InvalidBinOp(..))
                if matches!(op, Eq | Neq | Lt | Gt | GEq | LEq) =>
            {
                match self.invoke_custom_binary(op, lhs, rhs, ast_span) {
                    Ok(expr) => Ok(expr),
                    Err(e) => {
                        self.diag.err(original_diag);
                        Err(e)
                    }
                }
            }
            Err(original_diag @ CodeDiagnostic::ZstPointerOffset) => {
                // special case for ZST pointer offsets, which are a no-op
                self.diag.warn(original_diag);
                let temporary = self.make_local(lhs.ty, lhs.span);

                Ok(self.exprs.block(
                    [
                        ir::Statement::Expression(self.exprs.assign(temporary, lhs, lhs.span)),
                        ir::Statement::Expression(rhs),
                    ],
                    temporary,
                    ast_span,
                ))
            }
            Err(e) => Err(e).with_backtrace(&self.diag),
        }
    }

    fn lower_assign_op(
        &mut self,
        op: ast::BinOp,
        lhs: ast::ExprP<'ast>,
        rhs: ast::ExprP<'ast>,
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
            bail!(self, CodeDiagnostic::CannotAssignToRValue);
        }

        if lhs.is_const {
            bail!(self, CodeDiagnostic::CannotAssignToConst);
        }

        match self.typecheck_binary(op, lhs, rhs) {
            Ok(_) => {}
            Err(original_diag @ CodeDiagnostic::ZstPointerOffset) => {
                // special case for ZST pointer offsets, which are a no-op
                self.diag.warn(original_diag);
                return Ok(self.exprs.block(
                    [
                        ir::Statement::Expression(lhs),
                        ir::Statement::Expression(rhs),
                    ],
                    self.exprs
                        .void(self.types.void(), ir::ValueType::RValue, ast_span),
                    ast_span,
                ));
            }
            Err(e) => return Err(e).with_backtrace(&self.diag),
        }

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
            bail!(self, CodeDiagnostic::CannotAssignToRValue);
        }

        if lhs.is_const {
            bail!(self, CodeDiagnostic::CannotAssignToConst);
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
                    bail!(
                        self,
                        CodeDiagnostic::MismatchedBranchTypes(
                            self.ctx.type_name(then.ty).unwrap(),
                            self.ctx.type_name(els.ty).unwrap()
                        )
                    );
                }
            } else {
                bail!(
                    self,
                    CodeDiagnostic::MismatchedBranchTypes(
                        self.ctx.type_name(then.ty).unwrap(),
                        self.ctx.type_name(els.ty).unwrap()
                    )
                );
            }
        }

        // This is a bit nasty since runtime::in_const_context behaves differently in
        // const context and in runtie context, so we don't want to warn if that is the case
        // but also exclude inreachable branches in codegen (so we don't accidentally codegen
        // const-only code)
        let mut const_cond = None;
        let child = self.fork(true);
        match ir::const_eval::ConstEvaluator::new(
            child.ctx.global_ctx.clone(),
            child.diag.fork(),
            child.ctx.malloc_bag.clone(),
            child.ctx.ir,
            child.local_types.iter().map(|(k, v)| (*k, *v)),
        )
        .const_eval(cond)
        {
            Ok(Value::Bool(for_const_eval)) => {
                match ir::const_eval::ConstEvaluator::for_codegen(
                    child.ctx.global_ctx.clone(),
                    child.diag.fork(),
                    child.ctx.malloc_bag.clone(),
                    child.ctx.ir,
                    child.local_types.iter().map(|(k, v)| (*k, *v)),
                )
                .const_eval(cond)
                {
                    Ok(Value::Bool(for_codegen)) => {
                        if for_const_eval == for_codegen {
                            if matches!(cond_.kind, ast::ExprKind::Tag("loop_condition", _))
                                && for_codegen
                            {
                                self.diag.warn(CodeDiagnostic::WhileTrue);
                            } else {
                                self.diag
                                    .warn(CodeDiagnostic::ConstantCondition(for_const_eval));
                            }
                        }
                        const_cond = Some(for_codegen);
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        Ok(self.exprs.if_then(cond, then, els, const_cond, ast_span))
    }

    fn static_cond_matches(&mut self, cond: ast::ExprP<'ast>) -> Result<bool, AluminaError> {
        let mut child = self.fork(false);
        let ir_expr = child.lower_expr(cond, Some(child.types.builtin(BuiltinType::Bool)))?;
        let ret = ir::const_eval::ConstEvaluator::new(
            child.ctx.global_ctx.clone(),
            child.diag.fork(),
            child.ctx.malloc_bag.clone(),
            child.ctx.ir,
            child.local_types.iter().map(|(k, v)| (*k, *v)),
        )
        .const_eval(ir_expr)
        .and_then(|v| match v {
            Value::Bool(v) => Ok(v),
            _ => Err(mismatch!(
                self,
                self.types.builtin(BuiltinType::Bool),
                ir_expr.ty
            )),
        })?;

        Ok(ret)
    }

    fn lower_typecheck(
        &mut self,
        value: ast::ExprP<'ast>,
        ty: &ast::TyP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let value = self.lower_expr(value, None)?;
        let ty = self.lower_type_unrestricted(ty)?;
        let value = matches!(
            self.check_protocol_bound(ty, value.ty)?,
            BoundCheckResult::Matches
        );

        Ok(self.exprs.literal(
            Value::Bool(value),
            self.types.builtin(BuiltinType::Bool),
            ast_span,
        ))
    }

    fn lower_static_if(
        &mut self,
        cond: ast::ExprP<'ast>,
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

    fn lower_static_for(
        &mut self,
        loop_var: ast::StaticForLoopVariable<'ast>,
        range: ast::ExprP<'ast>,
        body: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let range = self.lower_expr(range, None)?;
        if range.diverges() {
            return Ok(range);
        }

        let range_ref = self.r#ref(range, ast_span);
        let iter = self.call_lang_item(Lang::StaticForIter, [range.ty], [range_ref], ast_span)?;

        let iter_local = self.make_local(iter.ty, ast_span);
        let assign = self.exprs.assign(iter_local, iter, ast_span);

        let iter_ref = self.r#ref(iter_local, ast_span);
        let iter_next =
            self.call_lang_item(Lang::StaticForNext, [iter.ty], [iter_ref], ast_span)?;

        let mut evaluator = ir::const_eval::ConstEvaluator::new(
            self.ctx.global_ctx.clone(),
            self.diag.fork(),
            self.ctx.malloc_bag.clone(),
            self.ctx.ir,
            self.local_types.iter().map(|(k, v)| (*k, *v)),
        );

        enum StaticForLoopVariable {
            Single(ir::Id),
            Tuple(Vec<ir::Id>),
        }

        let loop_var = match loop_var {
            ast::StaticForLoopVariable::Single(id) => {
                let loop_variable_id = self.ctx.map_id(id);
                self.local_types.insert(loop_variable_id, iter_next.ty);
                StaticForLoopVariable::Single(loop_variable_id)
            }
            ast::StaticForLoopVariable::Tuple(ids) => match iter_next.ty {
                ir::Ty::Tuple(elems) => {
                    if ids.len() > elems.len() {
                        bail!(
                            self,
                            CodeDiagnostic::TooManyLoopVars(self.ctx.type_name(iter_next.ty)?)
                        );
                    }

                    let mut ir_ids = Vec::new();
                    for (id, ty) in ids.iter().zip(elems.iter()) {
                        let id = self.ctx.map_id(*id);
                        self.local_types.insert(id, *ty);
                        ir_ids.push(id);
                    }
                    StaticForLoopVariable::Tuple(ir_ids)
                }
                _ => return Err(mismatch!(self, "tuple", iter_next.ty)),
            },
        };

        evaluator.const_eval(assign)?;
        let mut stmts = Vec::new();

        let mut existing_defs: HashSet<_> = self.local_defs.iter().copied().collect();
        loop {
            let value = match evaluator.const_eval(iter_next) {
                Ok(val) => val,
                Err(AluminaError::CodeErrors(code))
                    if code.iter().all(|c| {
                        matches!(
                            c.kind,
                            CodeDiagnostic::CannotConstEvaluate(ConstEvalErrorKind::StopIteration)
                        )
                    }) =>
                {
                    break
                }
                Err(e) => return Err(e),
            };

            match loop_var {
                StaticForLoopVariable::Single(id) => {
                    self.const_replacements.insert(id, value);
                }
                StaticForLoopVariable::Tuple(ref ids) => {
                    if let Value::Tuple(values) = value {
                        for (id, value) in ids.iter().zip(values.iter()) {
                            self.const_replacements.insert(*id, *value);
                        }
                    } else {
                        ice!(self.diag, "expected tuple value");
                    }
                }
            }

            let (body, local_defs) = {
                let mut child = self.fork(false);
                let body = child.lower_expr(body, type_hint)?;

                (body, child.local_defs)
            };

            let label_replacements: HashMap<_, _> = IdUsageCounter::count_labels(body)?
                .into_iter()
                .filter_map(|(id, count)| (count > 0).then_some((id, self.ctx.ir.make_id())))
                .collect();

            let local_replacements: HashMap<_, _> = local_defs
                .into_iter()
                .filter_map(|def| {
                    if existing_defs.contains(&def) {
                        None
                    } else {
                        let new_id = self.ctx.ir.make_id();
                        self.local_defs.push(LocalDef {
                            id: new_id,
                            ty: def.ty,
                        });
                        existing_defs.insert(LocalDef {
                            id: new_id,
                            ty: def.ty,
                        });
                        Some((def.id, new_id))
                    }
                })
                .collect();

            let body = Folder::fold(
                body,
                self.ctx.ir,
                |expr| match expr.kind {
                    ir::ExprKind::Local(id) => Ok(local_replacements
                        .get(&id)
                        .copied()
                        .map(|id| self.exprs.local(id, expr.ty, expr.span))),
                    _ => Ok(None),
                },
                |stmt| match stmt {
                    ir::Statement::Label(id) => Ok(label_replacements
                        .get(id)
                        .copied()
                        .map(ir::Statement::Label)),
                    _ => Ok(None),
                },
            )?;

            stmts.push(body);

            if body.diverges() {
                return Ok(self.exprs.diverges(stmts, ast_span));
            }
        }

        Ok(self.exprs.block(
            stmts.into_iter().map(ir::Statement::Expression),
            self.exprs
                .void(self.types.void(), ir::ValueType::RValue, ast_span),
            ast_span,
        ))
    }

    fn lower_tag(
        &mut self,
        tag: &'ast str,
        inner: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let inner: &ir::Expr = self.lower_expr(inner, type_hint)?;

        Ok(self.exprs.tag(tag, inner, ast_span))
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
            _ => vec![],
        };

        let mut index = 0;
        let mut stmts = Vec::new();
        let mut lowered = Vec::with_capacity(exprs.len());

        for expr in exprs {
            let _guard = self.diag.push_span(expr.span);
            match expr.kind {
                ast::ExprKind::EtCetera(inner) => {
                    // type hint is None since we do not know the length beforehand. If
                    // the expression is a tuple expression, we could pull it out, but for now
                    // we just leave it as None.
                    let inner = self.lower_expr(inner, None)?;
                    let ir::Ty::Tuple(types) = inner.ty else {
                        return Err(mismatch!(self, "tuple", inner.ty));
                    };

                    let (tup, assign) = self.ensure_local(inner);
                    stmts.extend(assign);

                    for (i, ty) in types.iter().enumerate() {
                        let field = self.exprs.tuple_index(tup, i, ty, inner.span);
                        lowered.push(self.exprs.block(stmts.drain(..), field, inner.span));
                        index += 1;
                    }
                }
                _ => {
                    let hint = type_hints.get(index).copied().flatten();
                    let lowered_expr = self.lower_expr(expr, hint).map(|expr| {
                        if let Some(hint) = hint {
                            if let Ok(a) = self.try_coerce(hint, expr) {
                                return a;
                            }
                        }

                        expr
                    })?;
                    lowered.push(self.exprs.block(
                        stmts.drain(..),
                        lowered_expr,
                        lowered_expr.span,
                    ));
                    index += 1;
                }
            }
        }

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(lowered, ast_span));
        }

        let element_types: Vec<_> = lowered.iter().map(|e| e.ty).collect();
        let tuple_type = self.types.tuple(element_types);

        // Unpacking produced an empty tuple, but there may have been side effects
        // in the process, so we need to wrap the tuple in a block. This is slightly
        // involved because we care about evaluating the expressions in order.
        let ret = if stmts.is_empty() {
            self.exprs
                .tuple(lowered.into_iter().enumerate(), tuple_type, ast_span)
        } else if let Some(last) = lowered.last_mut() {
            // Attach the remaining statements after the last tuple element
            let (expr, stmt) = self.ensure_local(last);
            stmts.extend(stmt);

            *last = self.exprs.block(stmts, expr, ast_span);
            self.exprs
                .tuple(lowered.into_iter().enumerate(), tuple_type, ast_span)
        } else {
            let ret = self.exprs.void(tuple_type, ir::ValueType::RValue, ast_span);
            self.exprs.block(stmts, ret, ast_span)
        };

        Ok(ret)
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

        let ty = self.lower_type_for_value(target_type)?;

        if expr.ty == ty && !target_type.is_dynamic() {
            // ignore casts to same typee via a type alias or a placeholder, those can be
            // necessary in a different instantiation
            // of the generic method or platform.
            if self.raise_type(ty)? == target_type {
                self.diag.warn(CodeDiagnostic::UnnecessaryCast(
                    self.ctx.type_name(expr.ty).unwrap(),
                ));
            }
        }

        // If the type coerces automatically, no cast is required
        if let Ok(expr) = self.try_coerce(ty, expr) {
            return Ok(self.exprs.coerce(expr, ty, ast_span));
        }

        let ty_lang = self.ctx.lang_type_kind(ty);
        let expr_lang = self.ctx.lang_type_kind(expr.ty);

        // (Dangerous) Const to mut casts for lang objects
        match (ty_lang, expr_lang) {
            // &[T] -> &mut [T]
            (
                Some(LangKind::Slice(ir::Ty::Pointer(t1, _))),
                Some(LangKind::Slice(ir::Ty::Pointer(t2, _))),
            ) if *t1 == *t2 => {
                return self.call_lang_item(Lang::SliceConstCast, [*t1], [expr], ast_span);
            }
            // &dyn Proto -> &mut dyn Proto
            (Some(LangKind::Dyn(t1_proto, _)), Some(LangKind::Dyn(t2_proto, _)))
                if *t1_proto == *t2_proto =>
            {
                return self.call_lang_item(Lang::DynConstCast, [t1_proto], [expr], ast_span);
            }

            // &dyn Proto -> any pointer (unchecked downcast)
            (_, Some(LangKind::Dyn(t2_proto, t2_const))) if matches!(ty, ir::Ty::Pointer(_, _)) => {
                let call =
                    self.call_lang_item(Lang::DynData, [t2_proto, t2_const], [expr], ast_span)?;
                return Ok(self.exprs.cast(call, ty, ast_span));
            }
            _ => {}
        }

        match (expr.ty, ty) {
            // Numeric casts
            (ir::Ty::Builtin(a), ir::Ty::Builtin(b)) if a.is_numeric() && b.is_numeric() => {}
            // bool -> integer (but not vice-versa)
            (ir::Ty::Builtin(BuiltinType::Bool), ir::Ty::Builtin(b)) if b.is_numeric() => {}

            // Enums
            (ir::Ty::Item(a), ir::Ty::Builtin(b))
                if matches!(a.get().with_backtrace(&self.diag)?, ir::Item::Enum(_))
                    && b.is_numeric() => {}
            (ir::Ty::Builtin(a), ir::Ty::Item(b))
                if matches!(b.get().with_backtrace(&self.diag)?, ir::Item::Enum(_))
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

            _ => bail!(
                self,
                CodeDiagnostic::InvalidCast(
                    self.ctx.type_name(expr.ty).unwrap(),
                    self.ctx.type_name(ty).unwrap()
                )
            ),
        }

        Ok(self.exprs.cast(expr, ty, ast_span))
    }

    fn lower_loop(
        &mut self,
        body: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let loop_result = self.ctx.ir.make_id();
        let break_label = self.ctx.ir.make_id();
        let continue_label = self.ctx.ir.make_id();

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
            Some(ty) => {
                self.local_defs.push(ir::LocalDef {
                    id: loop_result,
                    ty,
                });
                self.exprs.block(
                    statements,
                    self.exprs.local(loop_result, ty, ast_span),
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
            .ok_or_else(|| self.diag.err(CodeDiagnostic::BreakOutsideOfLoop))?;

        let expr = expr
            .map(|e| self.lower_expr(e, loop_context.type_hint))
            .transpose()?;

        if expr.map(|e| e.diverges()).unwrap_or(false) {
            return Ok(expr.unwrap());
        }

        let break_ty = expr.map(|e| e.ty).unwrap_or_else(|| self.types.void());

        let slot_type = match self.local_types.entry(loop_context.loop_result) {
            Entry::Vacant(v) => {
                v.insert(break_ty);
                break_ty
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
            .ok_or_else(|| self.diag.err(CodeDiagnostic::ContinueOutsideOfLoop))?;

        Ok(self.exprs.goto(loop_context.continue_label, ast_span))
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

        let data = self.exprs.literal(
            Value::Bytes(self.ctx.ir.arena.alloc_slice_copy(value), 0),
            ptr_type,
            span,
        );
        let size = self.exprs.literal(
            Value::USize(value.len()),
            self.types.builtin(BuiltinType::USize),
            span,
        );

        self.call_lang_item(Lang::SliceNew, [ptr_type], [data, size], span)
    }

    fn call<I>(
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
            ir::ExprKind::Item(item) => {
                let func = item.get_function().with_backtrace(&self.diag)?;
                if func
                    .attributes
                    .contains(&ast::Attribute::Inline(ast::Inline::DuringMono))
                {
                    // no silent fallback to a regular function call, since the only thing that can go wrong is that
                    // the callee is not compatible with IR inlining, so this should not lead to surprises
                    let (expr, mut additional_defs) = IrInliner::inline(
                        self.diag.fork(),
                        self.ctx.ir,
                        func.body
                            .get()
                            .ok_or_else(|| self.diag.err(CodeDiagnostic::UnpopulatedItem))?
                            .expr,
                        func.args
                            .iter()
                            .zip(args.into_iter())
                            .map(|(a, b)| (a.id, b)),
                    )?;

                    self.local_defs.append(&mut additional_defs);

                    // The inlined function may return a lvalue, which would be very confusing. If this happens, we
                    // patch up the value kind. C will still consider it a lvalue, but that shouldn't matter.
                    if expr.value_type == ir::ValueType::LValue {
                        return Ok(ir::Expr::rvalue(expr.kind.clone(), expr.ty, span)
                            .alloc_on(self.ctx.ir));
                    } else {
                        return Ok(expr);
                    }
                }
            }
            _ => {}
        }
        Ok(self.exprs.call(callee, args, return_ty, span))
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
        let layout = self.ctx.vtable_layouts.get(protocol_types).ok_or_else(|| {
            self.diag.err(CodeDiagnostic::InternalError(
                "vtable layout not found".to_string(),
                Backtrace::capture().into(),
            ))
        })?;

        let Some((vtable_index, func)) = layout
            .methods
            .iter()
            .enumerate()
            .find(|(_, p)| p.name == name)
        else {
            return Ok(None);
        };

        if func.arg_types.len() != args.len() + 1 {
            bail!(
                self,
                CodeDiagnostic::ParamCountMismatch(func.arg_types.len() - 1, args.len())
            );
        }

        // We need to store the dyn object in a temporary as it may have been produced by
        // an expression with side effects.
        let key = self.ctx.ir.intern_type(ir::Ty::Tuple(protocol_types));

        let canonical = self_arg.ty.canonical_type();
        let local = self.make_local(canonical, ast_span);
        let tgt = self.autoref(self_arg, canonical, ast_span)?;
        let call = self.call_lang_item(
            Lang::DynVtableIndex,
            [key, dyn_ptr],
            [
                local,
                self.exprs.literal(
                    Value::USize(vtable_index),
                    self.types.builtin(BuiltinType::USize),
                    ast_span,
                ),
            ],
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
                    .mono_lang_item(Lang::DynConstCast, [key])?
                    .get_function()
                    .with_backtrace(&self.diag)?
                    .return_type;

                return Err(mismatch!(self, mut_dyn, self_arg.ty));
            }
        }

        let mut args = once(Ok(self.call_lang_item(
            Lang::DynData,
            [key, dyn_ptr],
            [local],
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

    #[allow(clippy::too_many_arguments)]
    fn lower_method_call(
        &mut self,
        self_arg: ast::ExprP<'ast>,
        unified_fn: Option<ast::ItemP<'ast>>,
        name: &'ast str,
        args: &[ast::ExprP<'ast>],
        generic_args: Option<&[ast::TyP<'ast>]>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<Option<ir::ExprP<'ir>>, AluminaError> {
        let ir_self_arg = self.lower_expr(self_arg, None)?;

        // Special case for struct fields (they have precedence over methods in .name resolution)
        if let ir::Ty::Item(item) = ir_self_arg.ty.canonical_type() {
            if let ir::Item::StructLike(_) = item.get().with_backtrace(&self.diag)? {
                let fields = self.struct_field_map(item)?;
                if fields.contains_key(name) {
                    // This is not a method, but a field (e.g. a function pointer), go back to lower_call
                    // and process it as usual.
                    return Ok(None);
                }
            }
        };

        let canonical = ir_self_arg.ty.canonical_type();

        if let Some(LangKind::Dyn(ir::Ty::Tuple(protocols), dyn_ptr)) =
            self.ctx.lang_type_kind(canonical)
        {
            if let Some(result) =
                self.lower_virtual_call(protocols, dyn_ptr, ir_self_arg, name, args, ast_span)?
            {
                return Ok(Some(result));
            }
        }

        let method = self
            .associated_fns(canonical)?
            .get(name)
            .copied()
            .or(unified_fn)
            .ok_or_else(|| {
                self.diag.err(CodeDiagnostic::MethodNotFound(
                    name.into(),
                    self.ctx.type_name(canonical).unwrap(),
                ))
            })?;

        let method = self.try_resolve_function(
            method,
            generic_args,
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
                let fun = item.get_function().with_backtrace(&self.diag)?;
                fn_arg_types = fun.args.iter().map(|p| p.ty).collect();
                (&fn_arg_types[..], fun.return_type)
            }
            _ => unreachable!(),
        };

        if arg_types.is_empty() {
            bail!(self, CodeDiagnostic::NotAMethod);
        }

        if arg_types.len() != args.len() + 1 {
            bail!(
                self,
                CodeDiagnostic::ParamCountMismatch(arg_types.len() - 1, args.len())
            );
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
        let ty = match ast_type {
            ast::Ty::Generic(ast::Ty::Item(n), _) | ast::Ty::Item(n) => {
                if let ast::Item::TypeDef(ast::TypeDef {
                    target: Some(target),
                    ..
                }) = n.get()
                {
                    let _guard = self
                        .ctx
                        .cycles
                        .guard((n, &[]))
                        .map_err(|_| self.diag.err(CodeDiagnostic::CycleDetected))?;

                    return self.resolve_ast_type(target);
                }

                ast_type
            }
            ast::Ty::Tag(_, inner) => self.resolve_ast_type(inner)?,
            ast::Ty::Placeholder(_) => {
                let ir_type = self.lower_type_for_value(ast_type)?;
                self.raise_type(ir_type)?
            }
            _ => ast_type,
        };

        Ok(ty)
    }

    fn resolve_defered_func(
        &mut self,
        spec: &ast::Defered<'ast>,
    ) -> Result<ast::ItemP<'ast>, AluminaError> {
        let ty = self.resolve_ast_type(spec.ty)?;
        let associated_fns = self.associated_fns_for_ast(ty)?;
        let func = associated_fns.get(spec.name).ok_or_else(|| {
            self.diag
                .err(CodeDiagnostic::UnresolvedItem(spec.name.to_string()))
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
                        type_hint,
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
            ast::ExprKind::Field(e, field, unified_fn, generic_args) => {
                // Methods are resolved in the following order - field has precedence, then associated
                // functions, then free functions with UFCS. We never want UFCS to shadow native fields
                // and methods.
                match self.lower_method_call(
                    e,
                    *unified_fn,
                    field,
                    args,
                    *generic_args,
                    type_hint,
                    ast_span,
                )? {
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
            ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag)? {
                ir::Item::Closure(closure) => {
                    self_arg = Some(self.r#ref(callee, callee.span));

                    let fun_item = closure.function.get().unwrap();
                    let fun = fun_item.get_function().with_backtrace(&self.diag)?;
                    fn_arg_types = fun.args.iter().skip(1).map(|p| p.ty).collect();

                    (
                        &fn_arg_types[..],
                        fun.return_type,
                        self.exprs.function(fun_item, callee.span),
                    )
                }
                ir::Item::Function(fun) => {
                    if fun.varargs {
                        varargs = true;
                    }
                    fn_arg_types = fun.args.iter().map(|p| p.ty).collect();

                    (&fn_arg_types[..], fun.return_type, callee)
                }
                _ => {
                    bail!(self, CodeDiagnostic::FunctionOrStaticExpectedHere);
                }
            },
            _ => {
                bail!(self, CodeDiagnostic::FunctionOrStaticExpectedHere);
            }
        };

        if !varargs && (arg_types.len() != args.len()) {
            bail!(
                self,
                CodeDiagnostic::ParamCountMismatch(arg_types.len(), args.len())
            );
        }

        if varargs && (arg_types.len() > args.len()) {
            bail!(
                self,
                CodeDiagnostic::ParamCountMismatch(arg_types.len(), args.len())
            );
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
                    item.get().with_backtrace(&self.diag)?,
                    ir::Item::Function(_)
                ) =>
            {
                let fun = item.get_function().with_backtrace(&self.diag)?;
                fn_arg_types = fun.args.iter().map(|p| p.ty).collect();
                (Some(&fn_arg_types[..]), Some(fun.return_type))
            }
            _ => (None, None),
        };

        let result = match kind {
            ast::FnKind::Normal(item) => {
                if let ast::Item::Intrinsic(_) = item.get() {
                    bail!(self, CodeDiagnostic::IntrinsicsAreSpecialMkay);
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
                            id: self.ctx.map_id(binding.id),
                            name: Some(binding.name.alloc_on(self.ctx.ir)),
                            ty: expr.ty,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                let key = self.get_mono_key(func_item, &[], false)?;
                let closure_ty = match self.ctx.finished.entry(key.clone()) {
                    // The cell may be empty at this point if we are dealing with recursive references
                    // In this case, we will just return the item as is, but it will not
                    // be populated until the top-level item is finished.
                    Entry::Occupied(entry) => self.types.named(entry.get()),
                    Entry::Vacant(entry) => {
                        let closure = self.ctx.ir.make_item();
                        self.ctx.reverse_map.insert(closure, key.clone());
                        entry.insert(closure);

                        closure.assign(ir::Item::Closure(ir::Closure {
                            data: ir::StructLike {
                                name: None,
                                attributes: &[],
                                fields: fields.clone().alloc_on(self.ctx.ir),
                                span: None,
                                is_union: false,
                            },
                            function: OnceCell::new(),
                        }));

                        let closure_ty = self.types.named(closure);
                        let item = self.try_resolve_function(
                            func_item,
                            generic_args,
                            Some(
                                self.exprs
                                    .local(self.ctx.ir.make_id(), closure_ty, ast_span),
                            ),
                            None,
                            return_type_hint,
                            args_hint,
                        )?;

                        closure
                            .get_closure()
                            .with_backtrace(&self.diag)?
                            .function
                            .set(item)
                            .unwrap();

                        closure_ty
                    }
                };

                self.exprs.r#struct(
                    fields.into_iter().zip(bound_values).map(|(f, e)| (f.id, e)),
                    closure_ty,
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

    pub fn ensure_local(
        &mut self,
        expr: ir::ExprP<'ir>,
    ) -> (ir::ExprP<'ir>, Option<ir::Statement<'ir>>) {
        match expr.kind {
            ir::ExprKind::Local(_) => (expr, None),
            _ => {
                let local = self.make_local(expr.ty, expr.span);
                let stmt = ir::Statement::Expression(self.exprs.assign(local, expr, None));
                (local, Some(stmt))
            }
        }
    }

    fn lower_tuple_index(
        &mut self,
        tup: ast::ExprP<'ast>,
        index: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let tup = self.lower_expr(tup, None)?;
        let index = self.tuple_index_ranges(index)?;

        let result = match tup.ty.canonical_type() {
            ir::Ty::Tuple(types) => {
                let mut tup = tup;
                while let ir::Ty::Pointer(_, _) = tup.ty {
                    tup = self.exprs.deref(tup, ast_span);
                }

                match index {
                    TupleIndex::Single(index) => {
                        if index >= types.len() {
                            bail!(self, CodeDiagnostic::TupleIndexOutOfBounds);
                        }
                        self.exprs.tuple_index(tup, index, types[index], ast_span)
                    }
                    TupleIndex::Range(start, end) => {
                        types
                            .get((start, end))
                            .ok_or_else(|| self.diag.err(CodeDiagnostic::TupleIndexOutOfBounds))?;

                        let (tup, stmt) = self.ensure_local(tup);
                        let sliced = types
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| (start, end).contains(i))
                            .map(|(idx, ty)| self.exprs.tuple_index(tup, idx, ty, ast_span))
                            .collect::<Vec<_>>();

                        let ty = self.types.tuple(sliced.iter().map(|e| e.ty));
                        let ret = self
                            .exprs
                            .tuple(sliced.into_iter().enumerate(), ty, ast_span);

                        self.exprs.block(stmt, ret, ast_span)
                    }
                }
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
        generic_args: Option<&'ast [ast::TyP<'ast>]>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let obj = self.lower_expr(obj, None)?;

        if generic_args.is_some() {
            bail!(self, CodeDiagnostic::UnexpectedGenericArgs);
        }

        let result = match obj.ty.canonical_type() {
            ir::Ty::Item(item) => {
                let field_map = self.struct_field_map(item)?;
                let field = field_map.get(field).ok_or_else(|| {
                    self.diag
                        .err(CodeDiagnostic::UnresolvedItem(field.to_string()))
                })?;

                let mut obj = obj;
                while let ir::Ty::Pointer(_, _) = obj.ty {
                    obj = self.exprs.deref(obj, ast_span);
                }

                self.exprs.field(obj, field.id, field.ty, ast_span)
            }
            _ => bail!(self, CodeDiagnostic::StructLikeExpectedHere),
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
        let indexee_hint =
            if let Some(LangKind::Range(bound_ty, _)) = self.ctx.lang_type_kind(index.ty) {
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
        if let ir::Ty::Array(elem, len) = indexee.ty {
            if let Ok(index) = self.try_coerce(self.types.builtin(BuiltinType::USize), index) {
                if *len == 0 {
                    return Ok(self.exprs.deref(
                        self.exprs.literal(
                            Value::USize(0),
                            self.types.pointer(elem, indexee.is_const),
                            ast_span,
                        ),
                        ast_span,
                    ));
                }
                return Ok(self.exprs.index(indexee, index, ast_span));
            }
        }

        let ptr_ty = if let Some(LangKind::Slice(ptr_ty)) = self.ctx.lang_type_kind(indexee.ty) {
            ptr_ty
        } else {
            // Try slicifying the indexee
            let canonical = indexee.ty.canonical_type();
            indexee = self.autoref(indexee, self.types.pointer(canonical, true), ast_span)?;
            indexee = self.call_lang_item(
                Lang::SliceSlicify,
                [canonical, indexee.ty],
                [indexee],
                ast_span,
            )?;

            if let Some(LangKind::Slice(ptr_ty)) = self.ctx.lang_type_kind(indexee.ty) {
                ptr_ty
            } else {
                ice!(self.diag, "slice_slicify did not return a slice");
            }
        };

        if let Some(LangKind::Range(_, _)) = self.ctx.lang_type_kind(index.ty) {
            self.call_lang_item(
                Lang::SliceRangeIndex,
                [ptr_ty, index.ty],
                [indexee, index],
                ast_span,
            )
        } else {
            let index = self.try_coerce(self.types.builtin(BuiltinType::USize), index)?;
            let call =
                self.call_lang_item(Lang::SliceIndex, [ptr_ty], [indexee, index], ast_span)?;
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
            Some(ty) => self.ctx.lang_type_kind(ty).and_then(|kind| {
                if let LangKind::Range(inner, _) = kind {
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

                self.call_lang_item(
                    if inclusive {
                        Lang::RangeInclusiveNew
                    } else {
                        Lang::RangeNew
                    },
                    [bound_ty],
                    [lower, upper],
                    ast_span,
                )?
            }
            (Some(lower), None) => {
                let lower = self.try_coerce(bound_ty, lower)?;
                self.call_lang_item(Lang::RangeFromNew, [bound_ty], [lower], ast_span)?
            }
            (None, Some(upper)) => {
                let upper = self.try_coerce(bound_ty, upper)?;
                self.call_lang_item(
                    if inclusive {
                        Lang::RangeToInclusiveNew
                    } else {
                        Lang::RangeToNew
                    },
                    [bound_ty],
                    [upper],
                    ast_span,
                )?
            }
            (None, None) => self.call_lang_item(Lang::RangeFullNew, [bound_ty], [], ast_span)?,
        };

        Ok(result)
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
            bail!(self, CodeDiagnostic::NotInAFunctionScope);
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

    fn lower_yield(
        &mut self,
        inner: Option<ast::ExprP<'ast>>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.yield_type.is_none() {
            bail!(self, CodeDiagnostic::YieldOutsideOfCoroutine);
        }

        if self.defer_context.as_ref().is_some_and(|d| d.in_defer) {
            bail!(self, CodeDiagnostic::YieldInDefer);
        }

        let inner = inner
            .map(|inner| self.lower_expr(inner, self.yield_type))
            .transpose()?
            .unwrap_or_else(|| {
                self.exprs
                    .void(self.types.void(), ir::ValueType::RValue, ast_span)
            });

        if inner.diverges() {
            return Ok(inner);
        }
        let val: &ir::Expr<'ir> = self.try_coerce(self.yield_type.unwrap(), inner)?;
        let val_ref = self.r#ref(val, ast_span);

        let out = self.make_local(self.recv_type.unwrap(), ast_span);
        let out_ref = self.exprs.r#ref(out, ast_span);

        let cond = self.call_lang_item(
            Lang::CoroutineYield,
            [self.yield_type.unwrap(), self.recv_type.unwrap()],
            [val_ref, out_ref],
            ast_span,
        )?;
        let void = self
            .exprs
            .void(self.types.void(), ir::ValueType::RValue, ast_span);
        let early_return = self.make_return(void, ast_span)?;
        Ok(self.exprs.if_then(cond, early_return, out, None, ast_span))
    }

    fn lower_defer(
        &mut self,
        inner: ast::ExprP<'ast>,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if self.return_type.is_none() {
            bail!(self, CodeDiagnostic::NotInAFunctionScope);
        }

        if !self.loop_contexts.is_empty() && !self.tentative {
            self.diag.warn(CodeDiagnostic::DeferInALoop);
        }

        match self.defer_context.as_mut() {
            None => {
                let mut ctx = DeferContext::new(self.ctx.ir.make_id(), self.ctx.ir.make_id());
                ctx.in_defer = true;
                self.local_defs.push(ir::LocalDef {
                    id: ctx.return_local,
                    ty: self.return_type.unwrap(),
                });
                self.defer_context = Some(ctx);
            }
            Some(ctx) if ctx.in_defer => bail!(self, CodeDiagnostic::DeferInDefer),
            Some(ctx) => ctx.in_defer = true,
        };

        // cannot have defer_context borrowed over this point
        let inner = self.lower_expr(inner, None);
        let defer_context = self.defer_context.as_mut().unwrap();
        defer_context.in_defer = false;
        let inner = inner?;

        let defer_flag = self.ctx.ir.make_id();
        self.local_defs.push(ir::LocalDef {
            id: defer_flag,
            ty: self.types.builtin(BuiltinType::Bool),
        });

        defer_context.defered.push((defer_flag, inner));
        let ret = self.exprs.assign(
            self.exprs
                .local(defer_flag, self.types.builtin(BuiltinType::Bool), ast_span),
            self.exprs.literal(
                Value::Bool(true),
                self.types.builtin(BuiltinType::Bool),
                ast_span,
            ),
            ast_span,
        );

        Ok(self.exprs.tag("defer_assign", ret, ast_span))
    }

    fn lower_struct(
        &mut self,
        ty: ast::TyP<'ast>,
        inits: &[ast::FieldInitializer<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
        span: Option<ast::Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item = self.try_resolve_struct(ty, inits, type_hint)?;

        let field_map = self.struct_field_map(item)?;
        let mut uninitialized: HashSet<&'ast str> = field_map.keys().copied().collect();

        let is_union = item.get_struct_like().with_backtrace(&self.diag)?.is_union;

        let lowered = inits
            .iter()
            .enumerate()
            .map(|(idx, f)| {
                let _guard = self.diag.push_span(f.span);

                if is_union && idx > 0 {
                    self.diag.warn(CodeDiagnostic::UnionInitializerOverride);
                }

                uninitialized.remove(f.name);
                match field_map.get(&f.name) {
                    Some(field) => self
                        .lower_expr(f.value, Some(field.ty))
                        .and_then(|e| self.try_coerce(field.ty, e))
                        .map(|i| (*field, i)),
                    None => Err(self
                        .diag
                        .err(CodeDiagnostic::UnresolvedItem(f.name.to_string()))),
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
            lowered.into_iter().map(|(f, e)| (f.id, e)),
            struct_type,
            span,
        );

        if !is_union && !self.tentative {
            for u in uninitialized {
                self.diag
                    .warn(CodeDiagnostic::UninitializedField(u.to_string()));
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
            let mut expr = self.lower_expr(expr, first_elem_type.or(element_type_hint))?;
            if let Some(hint) = element_type_hint {
                if let Ok(a) = self.try_coerce(hint, expr) {
                    expr = a;
                }
            }

            if first_elem_type.is_none() {
                first_elem_type = Some(expr.ty);
            }
            lowered.push(self.try_coerce(first_elem_type.unwrap(), expr)?);
        }

        if lowered.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(lowered, ast_span));
        }

        let element_type = first_elem_type
            .or(element_type_hint)
            .ok_or_else(|| self.diag.err(CodeDiagnostic::TypeHintRequired))?;

        self.array_of(element_type, lowered, ast_span)
    }

    fn lower_enum_value(
        &mut self,
        ty: ast::ItemP<'ast>,
        id: ast::Id,
        _type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let item_cell = self.mono_item(ty, &[])?;
        let ir_id = self.ctx.map_id(id);
        let result = match item_cell.get() {
            Ok(ir::Item::Enum(item)) => self.exprs.cast(
                item.members.iter().find(|v| v.id == ir_id).unwrap().value,
                self.types.named(item_cell),
                ast_span,
            ),
            _ => bail!(self, CodeDiagnostic::CycleDetected),
        };

        Ok(result.alloc_on(self.ctx.ir))
    }

    fn lower_defered(
        &mut self,
        spec: &ast::Defered<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let ty = self.resolve_ast_type(spec.ty)?;
        // Currently only enum members can be defered during name/scope resolution (type::enum_value),
        // if it is not an enum, we assume it's an associated function. In the future there may be more
        // associated items that need to be handled.

        // Enum members have precedence over associated functions, but if the syntax indicates that
        // it is something that will be called (e.g. by calling it or specifying generic arguments),
        // it will be assumed to be a function, so there is some limited ambiguity.
        if let ast::Ty::Item(item) = ty {
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
        self.diag.overflow_check()?;

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
            ast::ExprKind::Cast(expr, ty) => self.lower_cast(expr, ty, type_hint, expr.span),
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
                self.lower_tuple_index(tup, index, type_hint, expr.span)
            }
            ast::ExprKind::Field(tup, field, _, generic_args) => {
                self.lower_field(tup, field, *generic_args, type_hint, expr.span)
            }
            ast::ExprKind::Call(func, args) => self.lower_call(func, args, type_hint, expr.span),
            ast::ExprKind::Array(elements) => {
                self.lower_array_expression(elements, type_hint, expr.span)
            }
            ast::ExprKind::EnumValue(ty, id) => {
                self.lower_enum_value(ty, *id, type_hint, expr.span)
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
            ast::ExprKind::Yield(inner) => self.lower_yield(*inner, type_hint, expr.span),
            ast::ExprKind::Fn(item, args) => self.lower_fn(*item, *args, type_hint, expr.span),
            ast::ExprKind::Static(item, args) => {
                self.lower_static(item, *args, type_hint, expr.span)
            }
            ast::ExprKind::Const(item, args) => self.lower_const(item, *args, type_hint, expr.span),
            ast::ExprKind::Defered(def) => self.lower_defered(def, type_hint, expr.span),
            ast::ExprKind::TypeCheck(value, ty) => {
                self.lower_typecheck(value, ty, type_hint, expr.span)
            }
            ast::ExprKind::StaticIf(cond, then, els) => {
                self.lower_static_if(cond, then, els, type_hint, expr.span)
            }
            ast::ExprKind::StaticFor(var, range, body) => {
                self.lower_static_for(*var, range, body, type_hint, expr.span)
            }
            ast::ExprKind::BoundParam(self_arg, field_id, bound_type) => {
                self.lower_bound_param(*self_arg, *field_id, *bound_type, type_hint, expr.span)
            }
            ast::ExprKind::Tag(tag, inner) => self.lower_tag(tag, inner, type_hint, expr.span),
            ast::ExprKind::EtCetera(_) => Err(self.diag.err(CodeDiagnostic::EtCeteraInUnsupported)),
            ast::ExprKind::EtCeteraMacro(_)
            | ast::ExprKind::MacroInvocation(_, _)
            | ast::ExprKind::Macro(_, _) => Err(self.diag.err(CodeDiagnostic::IsAMacro)),
        }
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
}
