use crate::ast::lang::Lang;
use crate::ast::{Attribute, BuiltinType, Span};
use crate::common::{ice, AluminaError, ArenaAllocatable, CodeDiagnostic, CodeErrorBuilder};
use crate::ir::const_eval::Value;
use crate::ir::infer::TypeInferer;
use crate::ir::{IntrinsicValueKind, ValueType};
use crate::{ast, ir};

use std::backtrace::Backtrace;

use std::iter::once;

use super::{bail, mismatch, MonoKey};

use alumina_boot_macros::AstSerializable;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, AstSerializable)]
pub enum Intr {
    SizeOf,
    AlignOf,
    LengthOf,
    TypeId,
    TypeName,
    NamedTypeName,
    Trap,
    Transmute,
    CompileFail,
    CompileWarn,
    CompileNote,
    Unreachable,
    Attributed,
    CodegenFunc,
    CodegenConst,
    CodegenTypeFunc,
    MakeVtable,
    EnumVariants,
    Uninitialized,
    Dangling,
    Zeroed,
    Asm,
    Volatile,
    InConstContext,
    IsConstEvaluable,
    ConstEval,
    ConstPanic,
    ConstWarning,
    ConstNote,
    ConstAlloc,
    ConstFree,
    Tag,
    TupleInvoke,
    Fields,
    StopIteration,
    ModulePath,
    HasAttribute,
    ValueOf,
    Expect,
    WithSpanOf,
}

pub fn intrinsic_kind(name: &str) -> Option<Intr> {
    use Intr::*;
    let ret = match name {
        "size_of" => SizeOf,
        "align_of" => AlignOf,
        "length_of" => LengthOf,
        "type_id" => TypeId,
        "type_name" => TypeName,
        "named_type_name" => NamedTypeName,
        "trap" => Trap,
        "transmute" => Transmute,
        "compile_fail" => CompileFail,
        "compile_warn" => CompileWarn,
        "compile_note" => CompileNote,
        "unreachable" => Unreachable,
        "attributed" => Attributed,
        "codegen_func" => CodegenFunc,
        "codegen_const" => CodegenConst,
        "codegen_type_func" => CodegenTypeFunc,
        "volatile" => Volatile,
        "vtable" => MakeVtable,
        "enum_variants" => EnumVariants,
        "asm" => Asm,
        "uninitialized" => Uninitialized,
        "dangling" => Dangling,
        "zeroed" => Zeroed,
        "in_const_context" => InConstContext,
        "is_const_evaluable" => IsConstEvaluable,
        "const_eval" => ConstEval,
        "const_panic" => ConstPanic,
        "const_warning" => ConstWarning,
        "const_note" => ConstNote,
        "const_alloc" => ConstAlloc,
        "const_free" => ConstFree,
        "tag" => Tag,
        "tuple_invoke" => TupleInvoke,
        "fields" => Fields,
        "stop_iteration" => StopIteration,
        "module_path" => ModulePath,
        "has_attribute" => HasAttribute,
        "value_of" => ValueOf,
        "expect" => Expect,
        "with_span_of" => WithSpanOf,
        _ => return None,
    };

    Some(ret)
}

/// Intrinsic functions
impl<'a, 'ast, 'ir> super::Mono<'a, 'ast, 'ir> {
    pub fn lower_intrinsic(
        &mut self,
        span: Option<ast::Span>,
        callee: &ast::Intrinsic,
        generic_args: &[ast::TyP<'ast>],
        args: &[ast::ExprP<'ast>],
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        use Intr::*;

        let generic_args = generic_args
            .iter()
            .map(|e| self.lower_type_unrestricted(e))
            .collect::<Result<Vec<_>, _>>()?;

        macro_rules! generic {
            ($n:literal) => {
                match generic_args.get($n) {
                    Some(arg) => arg,
                    None => ice!(self.diag, "not enough generic arguments to intrinsic"),
                }
            };
        }

        match callee.kind {
            // This one is special since it lowers the expression itself
            WithSpanOf => {
                let inner_expr = match args.first() {
                    Some(expr) => expr,
                    _ => ice!(self.diag, "not enough arguments to intrinsic"),
                };
                return self.intr_with_span_of(generic!(0), inner_expr, type_hint);
            }
            _ => {}
        }

        let args = args
            .iter()
            .map(|e| self.lower_expr(e, None))
            .collect::<Result<Vec<_>, _>>()?;

        macro_rules! arg {
            ($n:literal) => {
                match args.get($n) {
                    Some(arg) => arg,
                    None => ice!(self.diag, "not enough arguments to intrinsic"),
                }
            };
        }
        match callee.kind {
            MakeVtable => {
                if let ir::Ty::Tuple(inner) = generic!(0) {
                    self.generate_vtable(inner, generic!(1))
                } else {
                    ice!(
                        self.diag,
                        "creating a vtable with something that's not a tuple of protocols"
                    )
                }
            }
            EnumVariants => self.intr_enum_variants(generic!(0)),
            TypeName => self.intr_type_name(generic!(0), span),
            NamedTypeName => self.intr_named_type_name(generic!(0), span),
            SizeOf => self.intr_size_of(generic!(0), span),
            AlignOf => self.intr_align_of(generic!(0), span),
            TypeId => self.intr_type_id(generic!(0), span),
            LengthOf => self.intr_length_of(generic!(0), span),
            Trap => self.intr_trap(span),
            Transmute => self.intr_transmute(generic!(1), arg!(0), span),
            Volatile => self.intr_volatile(arg!(0), span),
            CompileFail => self.intr_compile_fail(arg!(0), span),
            CompileWarn => self.intr_compile_warn(arg!(0), span),
            CompileNote => self.intr_compile_note(arg!(0), span),
            Unreachable => self.intr_unreachable(span),
            Asm => self.intr_asm(arg!(0), span),
            CodegenFunc => self.intr_codegen_func(arg!(0), &args[1..], generic!(0), span),
            CodegenConst => self.intr_codegen_const(arg!(0), generic!(0), span),
            CodegenTypeFunc => self.intr_codegen_type_func(arg!(0), generic!(0), generic!(1), span),
            Uninitialized => self.intr_uninitialized(generic!(0), span),
            Zeroed => self.intr_zeroed(generic!(0), span),
            Dangling => self.intr_dangling(generic!(0), span),
            InConstContext => self.intr_in_const_context(span),
            ConstEval => self.intr_const_eval(arg!(0), span),
            ConstPanic => self.intr_const_panic(arg!(0), span),
            Tag => self.intr_tag(arg!(0), arg!(1), span),
            ConstWarning => self.intr_const_write(arg!(0), true, span),
            ConstNote => self.intr_const_write(arg!(0), false, span),
            ConstAlloc => self.intr_const_alloc(generic!(0), arg!(0), span),
            ConstFree => self.intr_const_free(arg!(0), span),
            IsConstEvaluable => self.intr_is_const_evaluable(arg!(0), span),
            TupleInvoke => self.intr_tuple_invoke(arg!(0), arg!(1), span),
            Fields => self.intr_fields(generic!(0)),
            Attributed => self.intr_attributed(arg!(0), generic!(0), span),
            StopIteration => self.intr_stop_iteration(span),
            ModulePath => self.intr_module_path(generic!(0), span),
            HasAttribute => self.intr_has_attribute(generic!(0), arg!(0), span),
            ValueOf => self.intr_value_of(generic!(0), span),
            Expect => self.intr_expect(arg!(0), arg!(1), span),
            WithSpanOf => unreachable!(),
        }
    }

    fn extract_const_string(&self, expr: ir::ExprP<'ir>) -> Result<&'ir str, AluminaError> {
        let mut evaluator = ir::const_eval::ConstEvaluator::new(
            self.ctx.global_ctx.clone(),
            self.diag.fork(),
            self.ctx.malloc_bag.clone(),
            self.ctx.ir,
            [],
        );

        match evaluator.const_eval(expr) {
            Ok(value) => {
                if let Some(r) = evaluator.extract_constant_string_from_slice(&value) {
                    Ok(std::str::from_utf8(r).unwrap())
                } else {
                    Err(mismatch!(self, "constant string", expr.ty))
                }
            }
            Err(e) => Err(e),
        }
    }

    fn intr_align_of(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let align = self
            .ctx
            .layouter
            .layout_of(ty)
            .with_backtrace(&self.diag)?
            .align;

        Ok(self.exprs.literal(
            Value::USize(align),
            self.types.builtin(BuiltinType::USize),
            span,
        ))
    }

    fn intr_size_of(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let size = self
            .ctx
            .layouter
            .layout_of(ty)
            .with_backtrace(&self.diag)?
            .size;

        Ok(self.exprs.literal(
            Value::USize(size),
            self.types.builtin(BuiltinType::USize),
            span,
        ))
    }

    fn intr_named_type_name(
        &mut self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let n = match ty {
            ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag)? {
                ir::Item::StructLike(s) => s.name,
                ir::Item::Protocol(s) => s.name,
                ir::Item::Function(s) => s.name,
                ir::Item::Enum(s) => s.name,
                ir::Item::Static(s) => s.name,
                ir::Item::Const(s) => s.name,
                _ => None,
            },
            _ => None,
        };

        Ok(n.map(|n| self.string_of(n.as_bytes(), span))
            .transpose()?
            .unwrap_or(self.exprs.void(self.types.void(), ValueType::RValue, span)))
    }

    fn intr_type_name(
        &mut self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.ctx.type_name(ty)?;
        self.string_of(name.as_bytes(), span)
    }

    fn intr_type_id(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        // just in case someone made a copy
        let interned = self.ctx.ir.intern_type(*ty);

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

    fn intr_length_of(
        &self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        match ty {
            ir::Ty::Array(_, len) => Ok(self.exprs.literal(
                Value::USize(*len),
                self.types.builtin(BuiltinType::USize),
                span,
            )),
            ir::Ty::Tuple(elems) => Ok(self.exprs.literal(
                Value::USize(elems.len()),
                self.types.builtin(BuiltinType::USize),
                span,
            )),
            _ => Err(self.diag.err(CodeDiagnostic::TypeMismatch(
                "array or slice".to_string(),
                format!("{:?}", ty),
            ))),
        }
    }

    fn intr_compile_fail(
        &self,
        reason: ir::ExprP<'ir>,
        _span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let reason = self.extract_const_string(reason)?;

        Err(self
            .diag
            .err(CodeDiagnostic::UserDefined(reason.to_string())))
    }

    fn intr_compile_warn(
        &self,
        reason: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let reason = self.extract_const_string(reason)?;

        self.diag
            .warn(CodeDiagnostic::UserDefined(reason.to_string()));

        Ok(self.exprs.void(self.types.void(), ValueType::RValue, span))
    }

    fn intr_compile_note(
        &self,
        reason: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let reason = self.extract_const_string(reason)?;

        self.diag
            .note(CodeDiagnostic::UserDefined(reason.to_string()));

        Ok(self.exprs.void(self.types.void(), ValueType::RValue, span))
    }

    fn intr_unreachable(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.unreachable(span))
    }

    fn intr_trap(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
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

    fn intr_transmute(
        &self,
        to: ir::TyP<'ir>,
        arg: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if to.assignable_from(arg.ty) {
            Ok(arg)
        } else {
            Ok(self
                .exprs
                .codegen_intrinsic(IntrinsicValueKind::Transmute(arg), to, span))
        }
    }

    fn intr_volatile(
        &self,
        arg: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        match arg.ty {
            ir::Ty::Pointer(inner, _) => {
                if inner.is_zero_sized() {
                    ice!(self.diag, "zero-sized volatile not supported")
                }
            }
            _ => {
                return Err(self.diag.err(CodeDiagnostic::TypeMismatch(
                    "pointer".to_string(),
                    format!("{:?}", arg.ty),
                )))
            }
        };

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::Volatile(arg), arg.ty, span))
    }

    fn intr_codegen_func(
        &self,
        name: ir::ExprP<'ir>,
        args: &[ir::ExprP<'ir>],
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.extract_const_string(name)?;

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

    fn intr_codegen_type_func(
        &self,
        name: ir::ExprP<'ir>,
        ty: ir::TyP<'ir>,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.extract_const_string(name)?;

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::SizeOfLike(name, ty), ret_ty, span))
    }

    fn intr_asm(
        &self,
        assembly: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let assembly = self.extract_const_string(assembly)?;

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::Asm(assembly), self.types.void(), span))
    }

    fn intr_codegen_const(
        &self,
        name: ir::ExprP<'ir>,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let name = self.extract_const_string(name)?;

        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::ConstLike(name), ret_ty, span))
    }

    fn intr_uninitialized(
        &self,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self
            .exprs
            .codegen_intrinsic(IntrinsicValueKind::Uninitialized, ret_ty, span))
    }

    fn intr_zeroed(
        &self,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let val = crate::ir::const_eval::make_zeroed(self.ctx.ir, ret_ty);

        Ok(self.exprs.literal(val, ret_ty, span))
    }

    fn intr_dangling(
        &self,
        ret_ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        if let ir::Ty::Pointer(inner, _) = ret_ty {
            Ok(self
                .exprs
                .codegen_intrinsic(IntrinsicValueKind::Dangling(inner), ret_ty, span))
        } else {
            Err(self.diag.err(CodeDiagnostic::TypeMismatch(
                "pointer".to_string(),
                format!("{:?}", ret_ty),
            )))
        }
    }

    fn intr_in_const_context(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.codegen_intrinsic(
            IntrinsicValueKind::InConstContext,
            self.types.builtin(BuiltinType::Bool),
            span,
        ))
    }

    fn intr_const_eval(
        &mut self,
        expr: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let mut evaluator = ir::const_eval::ConstEvaluator::new(
            self.ctx.global_ctx.clone(),
            self.diag.fork(),
            self.ctx.malloc_bag.clone(),
            self.ctx.ir,
            self.local_types.iter().map(|(k, v)| (*k, *v)),
        );

        let val = evaluator.const_eval(expr)?;

        Ok(self.exprs.literal(val, expr.ty, span))
    }

    fn intr_const_panic(
        &self,
        reason: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.tag(
            "const_only",
            self.exprs.codegen_intrinsic(
                IntrinsicValueKind::ConstPanic(reason),
                self.types.builtin(BuiltinType::Never),
                span,
            ),
            span,
        ))
    }

    fn intr_stop_iteration(&self, span: Option<Span>) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.tag(
            "const_only",
            self.exprs.codegen_intrinsic(
                IntrinsicValueKind::StopIteration,
                self.types.builtin(BuiltinType::Never),
                span,
            ),
            span,
        ))
    }

    fn intr_module_path(
        &mut self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let path = match ty {
            ir::Ty::Item(item) => {
                let MonoKey(ast_item, _, _, _) = self.ctx.reverse_lookup(item);
                self.ctx.ast.metadatum(ast_item).map(|m| m.path.to_string())
            }
            _ => None,
        };

        Ok(path
            .map(|n| self.string_of(n.as_bytes(), span))
            .transpose()?
            .unwrap_or(self.exprs.void(self.types.void(), ValueType::RValue, span)))
    }

    fn intr_tag(
        &self,
        tag: ir::ExprP<'ir>,
        value: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let tag = self.extract_const_string(tag)?;

        Ok(self.exprs.tag(tag, value, span))
    }

    fn intr_const_write(
        &self,
        reason: ir::ExprP<'ir>,
        warning: bool,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.tag(
            "const_only",
            self.exprs.codegen_intrinsic(
                IntrinsicValueKind::ConstWrite(reason, warning),
                self.types.void(),
                span,
            ),
            span,
        ))
    }

    fn intr_const_alloc(
        &self,
        ty: ir::TyP<'ir>,
        size: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.tag(
            "const_only",
            self.exprs.codegen_intrinsic(
                IntrinsicValueKind::ConstAlloc(ty, size),
                self.types.pointer(ty, false),
                span,
            ),
            span,
        ))
    }

    fn intr_const_free(
        &self,
        ptr: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        Ok(self.exprs.tag(
            "const_only",
            self.exprs.codegen_intrinsic(
                IntrinsicValueKind::ConstFree(ptr),
                self.types.void(),
                span,
            ),
            span,
        ))
    }

    fn intr_is_const_evaluable(
        &mut self,
        expr: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let child = self.fork(true);
        let ret = ir::const_eval::ConstEvaluator::new(
            child.ctx.global_ctx.clone(),
            child.diag.fork(),
            child.ctx.malloc_bag.clone(),
            child.ctx.ir,
            child.local_types.iter().map(|(k, v)| (*k, *v)),
        )
        .const_eval(expr)
        .is_ok();

        Ok(self.exprs.literal(
            Value::Bool(ret),
            self.types.builtin(BuiltinType::Bool),
            span,
        ))
    }

    fn intr_tuple_invoke(
        &mut self,
        callee: ir::ExprP<'ir>,
        tuple: ir::ExprP<'ir>,
        ast_span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let (local_expr, stmt) = self.ensure_local(tuple);

        let mut args: Vec<_> = match tuple.ty {
            ir::Ty::Tuple(args) => args
                .iter()
                .enumerate()
                .map(|(idx, t)| self.exprs.tuple_index(local_expr, idx, t, ast_span))
                .collect(),
            _ => ice!(self.diag, "tuple expected"),
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

        for (expected, arg) in arg_types.iter().zip(args.iter_mut()) {
            *arg = self.try_coerce(expected, arg)?;
        }

        if callee.diverges() || args.iter().any(|e| e.diverges()) {
            return Ok(self.exprs.diverges(once(callee).chain(args), ast_span));
        }

        if let Some(self_arg) = self_arg {
            args.insert(0, self_arg);
        }

        let ret = self.call(callee, args, return_type, ast_span)?;
        Ok(self.exprs.block(stmt, ret, ast_span))
    }

    fn generate_vtable(
        &mut self,
        protocol_types: &'ir [ir::TyP<'ir>],
        concrete_type: ir::TyP<'ir>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        for protocol_type in protocol_types.iter() {
            let protocol = match protocol_type {
                ir::Ty::Item(protocol) => protocol,
                _ => ice!(self.diag, "protocol expected"),
            };
            let proto_key = self.ctx.reverse_lookup(protocol);
            // Replace the dyn_self placeholder
            let args = std::iter::once(concrete_type)
                .chain(proto_key.1[1..].iter().copied())
                .collect::<Vec<_>>()
                .alloc_on(self.ctx.ir);
            let actual_protocol = self.mono_item(proto_key.0, args)?;
            let actual_protocol_type = self.types.named(actual_protocol);

            // We only rely on standard protocol bound matching to see if the vtable is compatible
            self.check_protocol_bounds(
                ast::ProtocolBoundsKind::All,
                concrete_type,
                vec![(None, actual_protocol_type, false)],
            )?;
        }

        let vtable_layout = self
            .ctx
            .vtable_layouts
            .get(protocol_types)
            .ok_or_else(|| {
                self.diag.err(CodeDiagnostic::InternalError(
                    "vtable layout not found".to_string(),
                    Backtrace::capture().into(),
                ))
            })?
            .methods;

        let associated_fns = self.associated_fns(concrete_type)?;
        let mut attrs = Vec::new();

        for func in vtable_layout {
            // If the function is not found, that can only mean that someone is trying to convert a `dyn` into another
            // dyn. If it were not so, the compiler would have errored earlier (when checking the protocol bounds).
            // We'd need to generate a thunk for it and it's not worth the hassle.
            let function = associated_fns
                .get(&func.name)
                .ok_or_else(|| self.diag.err(CodeDiagnostic::IndirectDyn))?;

            let candidate_fun = function.get_function();

            let mut type_inferer = TypeInferer::new(
                self.ctx.ast,
                self.ctx.ir,
                self.ctx,
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
                .map(|(p, t)| (p.ty, t))
                .chain(once((candidate_fun.return_type, func.return_type)));

            let monomorphized = match type_inferer.try_infer(None, infer_slots) {
                Some(placeholders) => {
                    self.mono_item(function, placeholders.alloc_on(self.ctx.ir))?
                }
                _ => ice!(self.diag, "cannot infer types while generating vtable"),
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

    fn intr_enum_variants(&mut self, ty: ir::TyP<'ir>) -> Result<ir::ExprP<'ir>, AluminaError> {
        let e = match ty {
            ir::Ty::Item(item) => item.get_enum().with_backtrace(&self.diag)?,
            _ => ice!(self.diag, "enum expected"),
        };

        let enum_variant_new = self.mono_lang_item(Lang::EnumVariantNew, [ty])?;
        let enum_variant_new_func = enum_variant_new.get_function().with_backtrace(&self.diag)?;

        let mut exprs = Vec::with_capacity(e.members.len());
        for member in e.members {
            let name = self.string_of(member.name.as_bytes(), None)?;
            let value = self.exprs.cast(member.value, ty, None);

            exprs.push(self.call_lang_item(Lang::EnumVariantNew, [ty], [name, value], None)?);
        }

        self.array_of(enum_variant_new_func.return_type, exprs, None)
    }

    fn intr_fields(&mut self, ty: ir::TyP<'ir>) -> Result<ir::ExprP<'ir>, AluminaError> {
        let s = match ty {
            ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag)? {
                ir::Item::StructLike(s) => s,
                ir::Item::Closure(c) => &c.data,
                _ => ice!(self.diag, "struct or union expected"),
            },
            _ => ice!(self.diag, "struct or union expected"),
        };

        let mut is_packed = false;
        let mut alignment = None;

        for attr in s.attributes {
            if let Attribute::Align(val) = attr {
                alignment = Some(*val);
            }
            if let Attribute::Packed(val) = attr {
                is_packed = true;
                alignment = Some(*val);
            }
        }

        let (_, field_layouts) = self
            .ctx
            .layouter
            .field_layout_of_aggregate(
                alignment,
                s.is_union,
                is_packed,
                s.fields.iter().map(|f| (f, f.ty)),
            )
            .with_backtrace(&self.diag)?;

        let mut exprs = Vec::with_capacity(s.fields.len());
        let mut offset = 0;
        for (maybe_field, layout) in field_layouts {
            if let Some(field) = maybe_field {
                let name = field.name.map(str::as_bytes).unwrap_or(&[]);
                let name = self.string_of(name, None)?;

                let offset = self.exprs.literal(
                    Value::USize(offset),
                    self.types.builtin(BuiltinType::USize),
                    None,
                );

                exprs.push(self.call_lang_item(
                    Lang::FieldDescriptorNew,
                    [ty, field.ty],
                    [name, offset],
                    None,
                )?);
            }
            offset += layout.size;
        }

        let ret_ty = self.types.tuple(exprs.iter().map(|e| e.ty));
        Ok(self
            .exprs
            .tuple(exprs.into_iter().enumerate(), ret_ty, None))
    }

    fn intr_attributed(
        &mut self,
        expr: ir::ExprP<'ir>,
        generic_args: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let attribute_name = self.extract_const_string(expr)?;

        let to_monomorphize: Vec<_> = self
            .ctx
            .ast
            .metadata()
            .iter()
            .filter_map(|(item, metadatum)| {
                metadatum
                    .attributes
                    .iter()
                    .any(|attr| matches!(attr, Attribute::Custom(n) if n.name == attribute_name))
                    .then_some(item)
            })
            .copied()
            .collect();

        let generic_args = match generic_args {
            ir::Ty::Tuple(args) => args,
            _ => ice!(self.diag, "tuple expected"),
        };

        let mut exprs = Vec::with_capacity(to_monomorphize.len());
        for item in to_monomorphize {
            let item = self.mono_item(item, generic_args)?;
            exprs.push(self.call_lang_item(
                Lang::TypeDescriptorNew,
                [self.types.named(item)],
                [],
                None,
            )?);
        }

        let ret_ty = self.types.tuple(exprs.iter().map(|e| e.ty));
        Ok(self
            .exprs
            .tuple(exprs.into_iter().enumerate(), ret_ty, span))
    }

    fn intr_has_attribute(
        &mut self,
        ty: ir::TyP<'ir>,
        expr: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let attribute_name = self.extract_const_string(expr)?;

        let val = match ty {
            ir::Ty::Item(item) => item
                .attributes()
                .iter()
                .any(|attr| matches!(attr, Attribute::Custom(n) if n.name == attribute_name)),
            _ => false,
        };

        Ok(self.exprs.literal(
            Value::Bool(val),
            self.types.builtin(BuiltinType::Bool),
            span,
        ))
    }

    fn intr_value_of(
        &mut self,
        ty: ir::TyP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        match ty {
            ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag)? {
                ir::Item::Const(c) => Ok(self.exprs.const_var(item, c.ty, span)),
                ir::Item::Static(c) => Ok(self.exprs.static_var(item, c.ty, span)),
                _ => ice!(self.diag, "const or static expected"),
            },
            _ => ice!(self.diag, "const or static expected"),
        }
    }

    fn intr_expect(
        &mut self,
        expr: ir::ExprP<'ir>,
        to_be: ir::ExprP<'ir>,
        span: Option<Span>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let mut evaluator = ir::const_eval::ConstEvaluator::new(
            self.ctx.global_ctx.clone(),
            self.diag.fork(),
            self.ctx.malloc_bag.clone(),
            self.ctx.ir,
            [],
        );

        let r#bool = self.types.builtin(BuiltinType::Bool);
        if r#bool.assignable_from(expr.ty) {
            mismatch!(self, r#bool, expr.ty);
        }

        let to_be = match evaluator.const_eval(to_be)? {
            Value::Bool(v) => v,
            _ => ice!(self.diag, "expecting a const boolean"),
        };

        Ok(self.exprs.codegen_intrinsic(
            IntrinsicValueKind::Expect(expr, to_be),
            self.types.builtin(BuiltinType::Bool),
            span,
        ))
    }

    fn intr_with_span_of(
        &mut self,
        ty: ir::TyP<'ir>,
        inner: ast::ExprP<'ast>,
        type_hint: Option<ir::TyP<'ir>>,
    ) -> Result<ir::ExprP<'ir>, AluminaError> {
        let span = match ty {
            ir::Ty::Item(item) => match item.get().with_backtrace(&self.diag)? {
                ir::Item::Function(f) => f.span,
                ir::Item::Static(s) => s.span,
                ir::Item::Const(c) => c.span,
                ir::Item::Protocol(p) => p.span,
                ir::Item::StructLike(s) => s.span,
                ir::Item::Enum(e) => e.span,
                _ => None,
            },
            _ => None,
        };

        let _guard = self.diag.push_span(span);
        self.lower_expr(inner, type_hint)
    }
}
