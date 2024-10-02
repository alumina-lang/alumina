use crate::ast::{Attribute, BinOp, BuiltinType, Inline, Span, UnOp};
use crate::codegen::elide_zst::ZstElider;
use crate::codegen::types::TypeWriter;
use crate::codegen::{w, CName, CodegenCtx};
use crate::common::{AluminaError, CodeErrorBuilder};
use crate::diagnostics::DiagnosticsStack;
use crate::ir::const_eval::Value;
use crate::ir::layout::Layouter;
use crate::ir::{
    Const, Expr, ExprKind, ExprP, Function, Id, IntrinsicValueKind, LocalDef, Statement, Static,
    Ty, ValueType,
};

use std::fmt::Write;

pub struct FunctionWriter<'ir, 'gen> {
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    type_writer: &'gen TypeWriter<'ir, 'gen>,
    fn_decls: String,
    fn_bodies: String,
    indent: usize,
    debug_info: bool,
    in_const_init: bool,
    last_span: Option<Span>,
}

pub fn write_function_signature<'ir, 'gen>(
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    buf: &mut String,
    id: Id,
    item: &'ir Function<'ir>,
    is_static: bool,
    is_body: bool,
) -> Result<(), AluminaError> {
    let name = ctx.get_name(id);
    let mut is_inline = false;

    let mut attributes = if item.attributes.contains(&Attribute::Inline(Inline::Always)) {
        is_inline = true;
        "__attribute__((always_inline)) inline ".to_string()
    } else if item.attributes.contains(&Attribute::Inline(Inline::Never)) {
        "__attribute__((noinline)) ".to_string()
    } else if item
        .attributes
        .contains(&Attribute::Inline(Inline::Default))
    {
        is_inline = true;
        "inline ".to_string()
    } else if item.attributes.contains(&Attribute::StaticConstructor) {
        "__attribute__((constructor)) ".to_string()
    } else {
        "".to_string()
    };

    if item.attributes.contains(&Attribute::Cold) {
        attributes = format!("__attribute__((cold)) {}", attributes);
    }

    if item.return_type.is_never() {
        attributes = format!("_Noreturn {}", attributes);
    }

    let return_type = if item.return_type.is_zero_sized() {
        let void = Ty::void();
        ctx.get_type(&void)
    } else {
        ctx.get_type(item.return_type)
    };

    if is_static || is_inline {
        w!(buf, "\n{}static {} {}(", attributes, return_type, name);
    } else {
        w!(buf, "\n{}{} {}(", attributes, return_type, name);
    }
    for (idx, arg) in item
        .args
        .iter()
        .filter(|arg| !arg.ty.is_zero_sized())
        .enumerate()
    {
        let name = ctx.get_name(arg.id);
        if idx > 0 {
            w!(buf, ", ");
        }
        w!(buf, "{} {}", ctx.get_type(arg.ty), name);
    }

    if item.varargs {
        if !item.args.is_empty() {
            w!(buf, ", ");
        }
        w!(buf, "...");
    }

    w!(buf, ")");

    let link_name = item
        .attributes
        .iter()
        .filter_map(|a| match a {
            Attribute::LinkName(name) => Some(*name),
            _ => None,
        })
        .next();

    if let Some(link_name) = link_name {
        if !is_body {
            w!(buf, " asm({})", link_name);
        }
    }

    Ok(())
}

impl<'ir, 'gen> FunctionWriter<'ir, 'gen> {
    pub fn new(
        ctx: &'gen CodegenCtx<'ir, 'gen>,
        type_writer: &'gen TypeWriter<'ir, 'gen>,
        size_estimate: usize,
    ) -> Self {
        Self {
            ctx,
            type_writer,
            fn_decls: String::with_capacity(size_estimate / 3 * 2),
            fn_bodies: String::with_capacity(size_estimate),
            indent: 0,
            debug_info: !ctx.global_ctx.has_option("no-debug-info"),
            in_const_init: false,
            last_span: None,
        }
    }

    fn endl(&self) -> &'static str {
        if self.debug_info {
            ""
        } else {
            "\n"
        }
    }

    fn write_binop(&mut self, op: BinOp) {
        match op {
            BinOp::And => w!(self.fn_bodies, "&&"),
            BinOp::Or => w!(self.fn_bodies, "||"),
            BinOp::BitAnd => w!(self.fn_bodies, "&"),
            BinOp::BitOr => w!(self.fn_bodies, "|"),
            BinOp::BitXor => w!(self.fn_bodies, "^"),
            BinOp::Eq => w!(self.fn_bodies, "=="),
            BinOp::Neq => w!(self.fn_bodies, "!="),
            BinOp::Lt => w!(self.fn_bodies, "<"),
            BinOp::LEq => w!(self.fn_bodies, "<="),
            BinOp::Gt => w!(self.fn_bodies, ">"),
            BinOp::GEq => w!(self.fn_bodies, ">="),
            BinOp::LShift => w!(self.fn_bodies, "<<"),
            BinOp::RShift => w!(self.fn_bodies, ">>"),
            BinOp::Plus => w!(self.fn_bodies, "+"),
            BinOp::Minus => w!(self.fn_bodies, "-"),
            BinOp::Mul => w!(self.fn_bodies, "*"),
            BinOp::Div => w!(self.fn_bodies, "/"),
            BinOp::Mod => w!(self.fn_bodies, "%"),
        }
    }

    fn write_unop(&mut self, op: UnOp) {
        match op {
            UnOp::Neg => w!(self.fn_bodies, "-"),
            UnOp::Not => w!(self.fn_bodies, "!"),
            UnOp::BitNot => w!(self.fn_bodies, "~"),
        }
    }

    fn write_string_literal(&mut self, bytes: &[u8]) {
        w!(self.fn_bodies, "(const uint8_t*)\"");

        let mut did_we_just_write_a_hex_escape = false;

        for c in bytes.iter().copied() {
            match c {
                b'\\' | b'\'' | b'"' | b' '..=b'~' => {
                    match c {
                        b'\\' => w!(self.fn_bodies, "\\\\"),
                        b'\'' => w!(self.fn_bodies, "\\'"),
                        b'"' => w!(self.fn_bodies, "\\\""),
                        _ => {
                            // C's escape sequences are very dumb. There is no limit on the
                            // length of a hexadecimal escape sequence. It would be easier to
                            // just hex-escape everything, but that makes the generated C
                            // less readable.
                            if did_we_just_write_a_hex_escape && c.is_ascii_hexdigit() {
                                w!(self.fn_bodies, "\"\"");
                            }
                            w!(self.fn_bodies, "{}", c as char);
                        }
                    }
                    did_we_just_write_a_hex_escape = false;
                }
                _ => {
                    w!(self.fn_bodies, "\\x{:02x}", c);
                    did_we_just_write_a_hex_escape = true;
                }
            }
        }
        w!(self.fn_bodies, "\"");
    }

    fn write_const_val(&mut self, val: Value) {
        match val {
            Value::Bool(val) => w!(self.fn_bodies, "{}", val as u8),
            Value::U8(val) => w!(self.fn_bodies, "{}", val),
            Value::U16(val) => w!(self.fn_bodies, "{}", val),
            Value::U32(val) => w!(self.fn_bodies, "{}ULL", val),
            Value::U64(val) => w!(self.fn_bodies, "{}ULL", val),
            Value::U128(val) => {
                w!(
                    self.fn_bodies,
                    "(((({0}){1}ULL) << 64)|(({0}){2}ULL))",
                    self.ctx.get_type(&Ty::Builtin(BuiltinType::U128)),
                    (val >> 64) as u64,
                    (val & 0xffff_ffff_ffff_ffff) as u64
                );
            }
            Value::I8(val) => w!(self.fn_bodies, "{}", val),
            Value::I16(val) => w!(self.fn_bodies, "{}", val),
            Value::I32(val) => w!(self.fn_bodies, "{}LL", val),
            Value::I64(val) => w!(self.fn_bodies, "{}LL", val),
            Value::I128(val) => {
                w!(
                    self.fn_bodies,
                    "(((({0}){1}ULL) << 64)|(({0}){2}ULL))",
                    self.ctx.get_type(&Ty::Builtin(BuiltinType::U128)),
                    ((val as u128) >> 64) as u64,
                    ((val as u128) & 0xffff_ffff_ffff_ffff) as u64
                );
            }
            Value::USize(val) => w!(self.fn_bodies, "{}ULL", val),
            Value::ISize(val) => w!(self.fn_bodies, "{}LL", val),
            Value::F32(val) => {
                if val.is_nan() {
                    w!(self.fn_bodies, "(0.0f/0.0f)");
                } else if val.is_infinite() {
                    if val.is_sign_positive() {
                        w!(self.fn_bodies, "(1.0f/0.0f)");
                    } else {
                        w!(self.fn_bodies, "(-1.0f/0.0f)");
                    }
                } else {
                    w!(self.fn_bodies, "{:?}f", val);
                }
            }
            Value::F64(val) => {
                if val.is_nan() {
                    w!(self.fn_bodies, "(0.0/0.0)");
                } else if val.is_infinite() {
                    if val.is_sign_positive() {
                        w!(self.fn_bodies, "(1.0/0.0)");
                    } else {
                        w!(self.fn_bodies, "(-1.0/0.0)");
                    }
                } else {
                    w!(self.fn_bodies, "{:?}", val);
                }
            }
            Value::Uninitialized => w!(self.fn_bodies, "{{0}}"),
            _ => unimplemented!(),
        }
    }

    fn indent(&mut self) {
        if !self.debug_info {
            w!(self.fn_bodies, "{}", " ".repeat(self.indent));
        }
    }

    pub fn write_local_def(&mut self, def: &LocalDef<'ir>) -> Result<(), AluminaError> {
        self.type_writer.add_type(def.ty)?;
        self.indent();
        w!(
            self.fn_bodies,
            "{} {};\n",
            self.ctx.get_type(def.ty),
            self.ctx.get_name(def.id)
        );

        Ok(())
    }

    pub fn write_stmt(
        &mut self,
        diag: &DiagnosticsStack,
        stmt: &Statement<'ir>,
    ) -> Result<(), AluminaError> {
        match stmt {
            Statement::Expression(e) => {
                if !(e.is_void() && e.is_unreachable()) {
                    self.indent();
                    self.write_expr(diag, e, false)?;
                    w!(self.fn_bodies, ";{}", self.endl());
                }
            }
            Statement::Label(id) => {
                self.indent();
                w!(
                    self.fn_bodies,
                    "{}: ;{}",
                    self.ctx.get_name(*id),
                    self.endl()
                );
            }
        }

        Ok(())
    }

    pub fn write_expr(
        &mut self,
        diag: &DiagnosticsStack,
        expr: &ExprP<'ir>,
        bare_block: bool,
    ) -> Result<(), AluminaError> {
        let _guard = diag.push_span(expr.span);

        self.type_writer.add_type(expr.ty)?;

        if self.debug_info {
            if let Some(span) = expr.span.map(|s| self.ctx.global_ctx.diag().map_span(s)) {
                let prev_line = self.last_span.map(|s| (s.file, s.line + 1));
                if prev_line != Some((span.file, span.line + 1)) {
                    if prev_line == Some((span.file, span.line)) {
                        w!(self.fn_bodies, "\n");
                    } else if let Some(filename) =
                        self.ctx.global_ctx.diag().get_file_path(span.file)
                    {
                        w!(
                            self.fn_bodies,
                            "\n#line {} {:?}\n",
                            span.line + 1,
                            filename.display()
                        );
                    }
                } else {
                    self.last_span = None;
                }
            }
        }

        match &expr.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                // Cast to C's automatic promotion of to int
                w!(self.fn_bodies, "({})(", self.ctx.get_type(expr.ty));
                self.write_expr(diag, lhs, false)?;
                self.write_binop(*op);
                self.write_expr(diag, rhs, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                self.write_expr(diag, lhs, false)?;
                self.write_binop(*op);
                w!(self.fn_bodies, "=");
                self.write_expr(diag, rhs, false)?;
            }
            ExprKind::Call(callee, args) => {
                self.write_expr(diag, callee, false)?;
                w!(self.fn_bodies, "(");
                for (idx, arg) in args
                    .iter()
                    .filter(|arg| !arg.ty.is_zero_sized())
                    .enumerate()
                {
                    if idx > 0 {
                        w!(self.fn_bodies, ", ");
                    }
                    self.write_expr(diag, arg, false)?;
                }
                w!(self.fn_bodies, ")");
            }
            ExprKind::Ref(inner) => {
                w!(self.fn_bodies, "(&");
                self.write_expr(diag, inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Deref(inner) => {
                w!(self.fn_bodies, "(*");
                self.write_expr(diag, inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Unary(op, inner) => {
                // Cast to C's automatic promotion of to int
                w!(self.fn_bodies, "({})(", self.ctx.get_type(expr.ty));
                self.write_unop(*op);
                self.write_expr(diag, inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Assign(lhs, rhs) => {
                self.write_expr(diag, lhs, false)?;
                w!(self.fn_bodies, "=");
                self.write_expr(diag, rhs, false)?;
            }
            ExprKind::Index(lhs, rhs) => {
                self.write_expr(diag, lhs, false)?;
                if let Ty::Array(_, _) = lhs.ty {
                    w!(self.fn_bodies, ".__data");
                }
                w!(self.fn_bodies, "[");
                self.write_expr(diag, rhs, false)?;
                w!(self.fn_bodies, "]");
            }
            ExprKind::Local(id) => {
                w!(self.fn_bodies, "{}", self.ctx.get_name(*id));
            }
            ExprKind::Item(item) => {
                w!(self.fn_bodies, "{}", self.ctx.get_name(item.id));
            }
            ExprKind::Block(stmts, ret) => {
                if bare_block {
                    for stmt in stmts.iter() {
                        self.write_stmt(diag, stmt)?;
                    }

                    if !ret.is_void() {
                        self.indent();
                        self.write_expr(diag, ret, true)?;
                    }
                } else {
                    w!(self.fn_bodies, "__extension__({{{}", self.endl());
                    for stmt in stmts.iter() {
                        self.write_stmt(diag, stmt)?;
                    }

                    if !(ret.is_void() && ret.is_unreachable()) {
                        self.indent();
                        self.write_expr(diag, ret, false)?;
                        w!(self.fn_bodies, ";{}", self.endl());
                    }
                    w!(self.fn_bodies, "}})");
                }
            }
            ExprKind::Lit(v) => match v {
                Value::Bytes(val, offset) => {
                    self.write_string_literal(&val[*offset..]);
                }
                _ => {
                    self.type_writer.add_type(expr.ty)?;
                    w!(self.fn_bodies, "(({})", self.ctx.get_type(expr.ty));
                    self.write_const_val(*v);
                    w!(self.fn_bodies, ")");
                }
            },
            ExprKind::Field(inner, field) => {
                self.write_expr(diag, inner, false)?;
                w!(self.fn_bodies, ".{}", self.ctx.get_name(*field));
            }
            ExprKind::TupleIndex(inner, idx) => {
                self.write_expr(diag, inner, false)?;
                w!(self.fn_bodies, "._{}", idx);
            }
            ExprKind::If(cond, then, els, _) if expr.ty.is_zero_sized() => {
                w!(self.fn_bodies, "if (");
                self.write_expr(diag, cond, false)?;
                w!(self.fn_bodies, ") {{{}", self.endl());
                self.indent += 2;
                self.write_expr(diag, then, true)?;
                self.indent -= 2;
                w!(self.fn_bodies, "{}", self.endl());

                self.indent();

                if els.is_void() || els.is_unreachable() {
                } else {
                    w!(self.fn_bodies, "}} else {{{}", self.endl());
                    self.indent += 2;
                    self.write_expr(diag, els, true)?;
                    self.indent -= 2;
                    w!(self.fn_bodies, "{}", self.endl());
                    self.indent();
                }

                w!(self.fn_bodies, "}}");
            }
            ExprKind::If(cond, then, els, _) => {
                w!(self.fn_bodies, "(");
                self.write_expr(diag, cond, false)?;
                w!(self.fn_bodies, "?");
                self.write_expr(diag, then, false)?;
                w!(self.fn_bodies, ":");
                self.write_expr(diag, els, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Cast(inner) => {
                self.type_writer.add_type(expr.ty)?;
                w!(self.fn_bodies, "(({})", self.ctx.get_type(expr.ty));
                self.write_expr(diag, inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Goto(label) => {
                w!(self.fn_bodies, "goto {}", self.ctx.get_name(*label));
            }
            ExprKind::Return(inner) => {
                w!(self.fn_bodies, "return ");
                self.write_expr(diag, inner, false)?;
            }
            ExprKind::Unreachable => {
                w!(self.fn_bodies, "__builtin_unreachable()");
            }
            ExprKind::Intrinsic(kind) => match kind {
                IntrinsicValueKind::SizeOfLike(n, ty) => {
                    self.type_writer.add_type(ty)?;
                    w!(self.fn_bodies, "{}({})", n, self.ctx.get_type(ty));
                }
                IntrinsicValueKind::FunctionLike(n) => {
                    w!(self.fn_bodies, "{}", n);
                }
                IntrinsicValueKind::ConstLike(n) => {
                    w!(self.fn_bodies, "{}", n);
                }
                IntrinsicValueKind::Asm(n) => {
                    w!(self.fn_bodies, "asm volatile({:?})", *n);
                }
                IntrinsicValueKind::Transmute(inner) => {
                    self.type_writer.add_type(inner.ty)?;
                    w!(
                        self.fn_bodies,
                        "(union {{ {} _1; {} _2; }}){{ ._1 = ",
                        self.ctx.get_type(inner.ty),
                        self.ctx.get_type(expr.ty)
                    );
                    self.write_expr(diag, inner, false)?;
                    w!(self.fn_bodies, " }}._2");
                }
                IntrinsicValueKind::Volatile(inner) => {
                    let Ty::Pointer(pointee, is_const) = expr.ty else {
                        unreachable!()
                    };

                    if *is_const {
                        w!(
                            self.fn_bodies,
                            "((volatile const {}*)",
                            self.ctx.get_type(pointee)
                        );
                    } else {
                        w!(
                            self.fn_bodies,
                            "((volatile {}*)",
                            self.ctx.get_type(pointee)
                        );
                    }

                    self.write_expr(diag, inner, false)?;
                    w!(self.fn_bodies, ")");
                }
                IntrinsicValueKind::Uninitialized => {
                    // I wish there was a prettier way to do this
                    w!(
                        self.fn_bodies,
                        "({{ {} __discard; __discard; }})",
                        self.ctx.get_type(expr.ty)
                    );
                }
                IntrinsicValueKind::Dangling(inner) => {
                    let layout = Layouter::new(self.ctx.global_ctx.clone())
                        .layout_of(inner)
                        .with_no_span()?;

                    w!(
                        self.fn_bodies,
                        "(({}){})",
                        self.ctx.get_type(expr.ty),
                        layout.align
                    );
                }
                IntrinsicValueKind::InConstContext => {
                    w!(self.fn_bodies, "({})0", self.ctx.get_type(expr.ty));
                }
                IntrinsicValueKind::Expect(expr, val) => {
                    w!(self.fn_bodies, "__builtin_expect(");
                    self.write_expr(diag, expr, false)?;
                    w!(self.fn_bodies, ", {})", *val as i32);
                }
                IntrinsicValueKind::ConstPanic(_)
                | IntrinsicValueKind::StopIteration
                | IntrinsicValueKind::ConstAlloc(_, _)
                | IntrinsicValueKind::ConstWrite(_, _)
                | IntrinsicValueKind::ConstFree(_) => {
                    unreachable!()
                }
            },
            ExprKind::Array(elems) => {
                self.type_writer.add_type(expr.ty)?;
                if !self.in_const_init {
                    w!(self.fn_bodies, "({})", self.ctx.get_type(expr.ty));
                }
                w!(self.fn_bodies, "{{.__data={{{}", self.endl());
                for elem in elems.iter() {
                    self.indent();
                    self.write_expr(diag, elem, false)?;
                    w!(self.fn_bodies, ",{}", self.endl());
                }
                self.indent();
                w!(self.fn_bodies, "}}}}");
            }
            ExprKind::Tuple(inits) => {
                self.type_writer.add_type(expr.ty)?;
                if !self.in_const_init {
                    w!(self.fn_bodies, "({})", self.ctx.get_type(expr.ty));
                }
                w!(self.fn_bodies, "{{");
                for init in inits.iter() {
                    if init.value.ty.is_zero_sized() {
                        continue;
                    }
                    w!(self.fn_bodies, "._{}=", init.index);
                    self.write_expr(diag, &init.value, false)?;
                    w!(self.fn_bodies, ",");
                }
                w!(self.fn_bodies, "}}");
            }
            ExprKind::Struct(inits) => {
                self.type_writer.add_type(expr.ty)?;
                if !self.in_const_init {
                    w!(self.fn_bodies, "({})", self.ctx.get_type(expr.ty));
                }
                w!(self.fn_bodies, "{{");
                for init in inits.iter() {
                    if init.value.ty.is_zero_sized() {
                        continue;
                    }
                    w!(self.fn_bodies, ".{}=", self.ctx.get_name(init.field));
                    self.write_expr(diag, &init.value, false)?;
                    w!(self.fn_bodies, ",");
                }
                w!(self.fn_bodies, "}}");
            }
            ExprKind::Tag(_tag, value) => {
                self.write_expr(diag, value, false)?;
            }
            ExprKind::Nop => {}
        }

        if bare_block {
            w!(self.fn_bodies, ";");
        }

        Ok(())
    }

    pub fn write_function_decl(
        &mut self,
        diag: &DiagnosticsStack,
        id: Id,
        item: &'ir Function<'ir>,
    ) -> Result<(), AluminaError> {
        let _guard = diag.push_span(item.span);
        let has_link_name = item
            .attributes
            .iter()
            .any(|a| matches!(a, Attribute::LinkName(..)));
        let should_export = item.attributes.contains(&Attribute::Export) || has_link_name;

        self.type_writer.add_type(item.return_type)?;
        for arg in item.args.iter() {
            self.type_writer.add_type(arg.ty)?;
        }

        if !has_link_name && (item.body.get().is_none() || should_export) {
            self.ctx
                .register_name(id, CName::Native(item.name.unwrap()));
            write_function_signature(self.ctx, &mut self.fn_decls, id, item, false, false)?;
        } else {
            self.ctx.register_name(
                id,
                match item.name {
                    Some(name) => CName::Mangled(name, self.ctx.make_id()),
                    None => CName::Id(self.ctx.make_id()),
                },
            );
            write_function_signature(
                self.ctx,
                &mut self.fn_decls,
                id,
                item,
                item.body.get().is_some()
                    && !should_export
                    && !self.ctx.global_ctx.has_cfg("debug"),
                false,
            )?;
        }

        w!(self.fn_decls, ";");

        Ok(())
    }

    pub fn write_static_decl(
        &mut self,
        diag: &DiagnosticsStack,
        id: Id,
        item: &'ir Static<'ir>,
    ) -> Result<(), AluminaError> {
        let _guard = diag.push_span(item.span);
        self.type_writer.add_type(item.ty)?;

        let attributes = if item.attributes.contains(&Attribute::ThreadLocal) {
            " __thread"
        } else {
            ""
        };

        if item.r#extern {
            self.ctx
                .register_name(id, CName::Native(item.name.unwrap()));
        } else if let Some(name) = item.name {
            self.ctx.register_name(id, CName::Mangled(name, id.id));
        }

        if !item.ty.is_zero_sized() {
            if item.r#extern {
                w!(
                    self.fn_decls,
                    "\nextern{} {} {};",
                    attributes,
                    self.ctx.get_type(item.ty),
                    self.ctx.get_name(id)
                );
            } else {
                w!(
                    self.fn_decls,
                    "\nstatic{} {} {};",
                    attributes,
                    self.ctx.get_type(item.ty),
                    self.ctx.get_name(id)
                );
            }
        }

        Ok(())
    }

    pub fn write_const_decl(
        &mut self,
        diag: &DiagnosticsStack,
        id: Id,
        item: &'ir Const<'ir>,
    ) -> Result<(), AluminaError> {
        let _guard = diag.push_span(item.span);
        if let Some(name) = item.name {
            self.ctx.register_name(id, CName::Mangled(name, id.id));
        }

        self.type_writer.add_type(item.ty)?;
        w!(
            self.fn_decls,
            "\nconst static {} {};",
            self.ctx.get_type(item.ty),
            self.ctx.get_name(id)
        );

        Ok(())
    }

    pub fn write_const(
        &mut self,
        diag: &DiagnosticsStack,
        id: Id,
        item: &'ir Const<'ir>,
    ) -> Result<(), AluminaError> {
        let _guard = diag.push_span(item.span);
        w!(
            self.fn_bodies,
            "\nconst static {} {} = ",
            self.ctx.get_type(item.ty),
            self.ctx.get_name(id)
        );

        self.in_const_init = true;
        let mut elider = ZstElider::new(diag.clone(), self.ctx.ir);
        let optimized = elider.elide_zst_expr(item.init).unwrap();
        let ret = self.write_expr(diag, &optimized, false);
        self.in_const_init = false;
        ret?;

        w!(self.fn_bodies, ";\n");

        Ok(())
    }

    pub fn write_function_body(
        &mut self,
        diag: &DiagnosticsStack,
        id: Id,
        item: &'ir Function<'ir>,
    ) -> Result<(), AluminaError> {
        let _guard = diag.push_span(item.span);
        let should_export = item.attributes.contains(&Attribute::Export);

        if item.body.get().is_none() {
            return Ok(());
        }

        write_function_signature(
            self.ctx,
            &mut self.fn_bodies,
            id,
            item,
            !should_export && !self.ctx.global_ctx.has_cfg("debug"),
            true,
        )?;

        let body = item.body.get().unwrap();

        let elider = ZstElider::new(diag.clone(), self.ctx.ir);
        let (local_defs, statements) = elider.elide_zst_func_body(body).unwrap();

        w!(self.fn_bodies, "{{\n");
        self.indent += 2;

        if item.args.iter().any(|a| a.ty.is_never()) {
            // functions that accept a parameter that is of never type can never be legally called,
            // so we add this to keep C compiler from complaining. If someone called it, it's already
            // UB.
            self.write_stmt(
                diag,
                &Statement::Expression(&Expr {
                    ty: &Ty::Builtin(BuiltinType::Never),
                    kind: ExprKind::Unreachable,
                    value_type: ValueType::RValue,
                    is_const: false,
                    span: None,
                }),
            )?;
        } else {
            for def in local_defs.iter() {
                self.write_local_def(def)?;
            }

            self.last_span = None;
            for stmt in statements.iter() {
                self.write_stmt(diag, stmt)?;
            }
        }
        self.indent -= 2;
        w!(self.fn_bodies, "}}\n");

        Ok(())
    }

    pub fn write(&self, buf: &mut String) {
        buf.reserve(self.fn_decls.len() + self.fn_bodies.len());
        buf.push_str(&self.fn_decls);
        buf.push_str(&self.fn_bodies);
    }
}
