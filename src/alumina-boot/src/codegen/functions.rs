use crate::{
    ast::{Attribute, BinOp, BuiltinType, CodegenType, UnOp},
    codegen::CName,
    common::AluminaError,
    intrinsics::CodegenIntrinsicKind,
    ir::{
        const_eval::Value, Expr, ExprKind, ExprP, Function, IrId, LocalDef, Statement, Static, Ty,
        ValueType,
    },
};

use super::{types::TypeWriter, w, CodegenCtx};

use std::{borrow::Cow, fmt::Write};

pub struct FunctionWriter<'ir, 'gen> {
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    type_writer: &'gen TypeWriter<'ir, 'gen>,
    fn_decls: String,
    fn_bodies: String,
    indent: usize,
}

/// Prevent "1f32" from being interpreted as an int constant
fn force_float(v: &str) -> Cow<'_, str> {
    if v.chars().all(|ch| ch.is_ascii_digit()) {
        Cow::Owned(format!("{}e0", v))
    } else {
        Cow::Borrowed(v)
    }
}

pub fn write_function_signature<'ir, 'gen>(
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    buf: &mut String,
    id: IrId,
    item: &'ir Function<'ir>,
    is_static: bool,
) -> Result<(), AluminaError> {
    let name = ctx.get_name(id);
    let mut is_inline = false;

    let mut attributes = if item.attributes.contains(&Attribute::ForceInline) {
        is_inline = true;
        "__attribute__((always_inline)) inline ".to_string()
    } else if item.attributes.contains(&Attribute::NoInline) {
        "__attribute__((noinline)) ".to_string()
    } else if item.attributes.contains(&Attribute::Inline) {
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
        ctx.get_type(&Ty::Builtin(BuiltinType::Void))
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
            Attribute::LinkName(size, name) => {
                Some(std::str::from_utf8(&name.as_slice()[..*size]).unwrap())
            }
            _ => None,
        })
        .next();

    if let Some(link_name) = link_name {
        w!(buf, " asm({})", link_name);
    }

    Ok(())
}

impl<'ir, 'gen> FunctionWriter<'ir, 'gen> {
    pub fn new(ctx: &'gen CodegenCtx<'ir, 'gen>, type_writer: &'gen TypeWriter<'ir, 'gen>) -> Self {
        Self {
            ctx,
            type_writer,
            fn_decls: String::with_capacity(512 * 1024),
            fn_bodies: String::with_capacity(512 * 1024),
            indent: 0,
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

    fn write_const_val(&mut self, val: Value) {
        match val {
            Value::Bool(val) => w!(
                self.fn_bodies,
                "{}",
                match val {
                    true => 1,
                    false => 0,
                }
            ),
            Value::U8(val) => w!(self.fn_bodies, "{}", val),
            Value::U16(val) => w!(self.fn_bodies, "{}", val),
            Value::U32(val) => w!(self.fn_bodies, "{}ULL", val),
            Value::U64(val) => w!(self.fn_bodies, "{}ULL", val),
            Value::U128(val) => {
                w!(
                    self.fn_bodies,
                    "((({0}){1}ULL) << 64)|(({0}){2}ULL)",
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
                    "((({0}){1}ULL) << 64)|(({0}){2}ULL)",
                    self.ctx.get_type(&Ty::Builtin(BuiltinType::U128)),
                    ((val as u128) >> 64) as u64,
                    ((val as u128) & 0xffff_ffff_ffff_ffff) as u64
                );
            }
            Value::USize(val) => w!(self.fn_bodies, "{}ULL", val),
            Value::ISize(val) => w!(self.fn_bodies, "{}LL", val),
            Value::F32(val) => w!(self.fn_bodies, "{}f", force_float(val)),
            Value::F64(val) => w!(self.fn_bodies, "{}", force_float(val)),
            _ => unimplemented!(),
        }
    }

    fn indent(&mut self) {
        w!(self.fn_bodies, "{}", " ".repeat(self.indent));
    }

    pub fn write_local_def(&mut self, def: &LocalDef<'ir>) -> Result<(), AluminaError> {
        self.type_writer.add_type(def.typ)?;
        self.indent();
        w!(
            self.fn_bodies,
            "{} {};\n",
            self.ctx.get_type(def.typ),
            self.ctx.get_name(def.id)
        );

        Ok(())
    }

    pub fn write_stmt(&mut self, stmt: &Statement<'ir>) -> Result<(), AluminaError> {
        match stmt {
            Statement::Expression(e) => {
                if !(e.is_void() && e.is_unreachable()) {
                    self.indent();
                    self.write_expr(e, false)?;
                    w!(self.fn_bodies, ";\n");
                }
            }
            Statement::Label(id) => {
                self.indent();
                w!(self.fn_bodies, "{}: ;\n", self.ctx.get_name(*id));
            }
        }

        Ok(())
    }

    pub fn write_expr(&mut self, expr: &ExprP<'ir>, bare_block: bool) -> Result<(), AluminaError> {
        self.type_writer.add_type(expr.ty)?;

        match &expr.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                w!(self.fn_bodies, "(");
                self.write_expr(lhs, false)?;
                self.write_binop(*op);
                self.write_expr(rhs, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                self.write_expr(lhs, false)?;
                self.write_binop(*op);
                w!(self.fn_bodies, "=");
                self.write_expr(rhs, false)?;
            }
            ExprKind::Call(callee, args) => {
                self.write_expr(callee, false)?;
                w!(self.fn_bodies, "(");
                for (idx, arg) in args
                    .iter()
                    .filter(|arg| !arg.ty.is_zero_sized())
                    .enumerate()
                {
                    if idx > 0 {
                        w!(self.fn_bodies, ", ");
                    }
                    self.write_expr(arg, false)?;
                }
                w!(self.fn_bodies, ")");
            }
            ExprKind::Fn(fun) => {
                w!(self.fn_bodies, "{}", self.ctx.get_name(fun.id));
            }
            ExprKind::Ref(inner) => {
                w!(self.fn_bodies, "(&");
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Deref(inner) => {
                w!(self.fn_bodies, "(*");
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Unary(op, inner) => {
                w!(self.fn_bodies, "(");
                self.write_unop(*op);
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Assign(lhs, rhs) => {
                self.write_expr(lhs, false)?;
                w!(self.fn_bodies, "=");
                self.write_expr(rhs, false)?;
            }
            ExprKind::Index(lhs, rhs) => {
                self.write_expr(lhs, false)?;
                if let Ty::Array(_, _) = lhs.ty {
                    w!(self.fn_bodies, ".__data");
                }
                w!(self.fn_bodies, "[");
                self.write_expr(rhs, false)?;
                w!(self.fn_bodies, "]");
            }
            ExprKind::Local(id) => {
                w!(self.fn_bodies, "{}", self.ctx.get_name(*id));
            }
            ExprKind::Static(item) => {
                w!(self.fn_bodies, "{}", self.ctx.get_name(item.id));
            }
            ExprKind::Lit(ref l) => match l {
                crate::ir::Lit::Str(v) => {
                    w!(self.fn_bodies, "(uint8_t*)\"");
                    for (_idx, c) in v.iter().enumerate() {
                        w!(self.fn_bodies, "\\x{:02x}", *c as u8);
                    }
                    w!(self.fn_bodies, "\"");
                }
                crate::ir::Lit::Int(v) => {
                    self.type_writer.add_type(expr.ty)?;
                    if matches!(
                        expr.ty,
                        Ty::Builtin(BuiltinType::U128) | Ty::Builtin(BuiltinType::I128)
                    ) {
                        self.type_writer.add_type(&Ty::Builtin(BuiltinType::U128))?;
                        w!(
                            self.fn_bodies,
                            "({0})(((({1}){2}ULL) << 64)|(({1}){3}ULL))",
                            self.ctx.get_type(expr.ty),
                            self.ctx.get_type(&Ty::Builtin(BuiltinType::U128)),
                            (v >> 64) as u64,
                            (v & 0xffff_ffff_ffff_ffff) as u64
                        );
                    } else {
                        w!(self.fn_bodies, "(({}){}ULL)", self.ctx.get_type(expr.ty), v);
                    }
                }
                crate::ir::Lit::Float(v) => {
                    self.type_writer.add_type(expr.ty)?;
                    if *expr.ty == Ty::Builtin(BuiltinType::F32) {
                        w!(self.fn_bodies, "({}f)", force_float(v));
                    } else {
                        w!(self.fn_bodies, "({})", force_float(v));
                    }
                }
                crate::ir::Lit::Bool(v) => {
                    w!(
                        self.fn_bodies,
                        "{}",
                        match v {
                            true => 1,
                            false => 0,
                        }
                    );
                }
                crate::ir::Lit::Null => {
                    self.type_writer.add_type(expr.ty)?;
                    w!(self.fn_bodies, "(({})0)", self.ctx.get_type(expr.ty));
                }
            },
            ExprKind::Block(stmts, ret) => {
                if bare_block {
                    for stmt in stmts.iter() {
                        self.write_stmt(stmt)?;
                    }

                    if !ret.is_void() {
                        self.indent();
                        self.write_expr(ret, true)?;
                    }
                } else {
                    w!(self.fn_bodies, "__extension__({{\n");
                    for stmt in stmts.iter() {
                        self.write_stmt(stmt)?;
                    }

                    if !(ret.is_void() && ret.is_unreachable()) {
                        self.indent();
                        self.write_expr(ret, false)?;
                        w!(self.fn_bodies, ";\n");
                    }
                    w!(self.fn_bodies, "}})");
                }
            }
            ExprKind::ConstValue(v) => {
                if let Value::Str(val) = v {
                    w!(self.fn_bodies, "(uint8_t*)\"");
                    for (_idx, c) in val.iter().enumerate() {
                        w!(self.fn_bodies, "\\x{:02x}", *c as u8);
                    }
                    w!(self.fn_bodies, "\"");
                } else {
                    self.type_writer.add_type(expr.ty)?;
                    w!(self.fn_bodies, "(({})", self.ctx.get_type(expr.ty));
                    self.write_const_val(*v);
                    w!(self.fn_bodies, ")");
                }
            }
            ExprKind::Field(inner, field) => {
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ".{}", self.ctx.get_name(*field));
            }
            ExprKind::TupleIndex(inner, idx) => {
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, "._{}", idx);
            }
            ExprKind::If(cond, then, els) if expr.ty.is_zero_sized() => {
                w!(self.fn_bodies, "if (");
                self.write_expr(cond, false)?;
                w!(self.fn_bodies, ") {{\n");
                self.indent += 2;
                self.write_expr(then, true)?;
                self.indent -= 2;
                w!(self.fn_bodies, "\n");

                self.indent();

                if els.is_void() || els.is_unreachable() {
                } else {
                    w!(self.fn_bodies, "}} else {{\n");
                    self.indent += 2;
                    self.write_expr(els, true)?;
                    self.indent -= 2;
                    w!(self.fn_bodies, "\n");
                    self.indent();
                }

                w!(self.fn_bodies, "}}");
            }
            ExprKind::If(cond, then, els) => {
                w!(self.fn_bodies, "(");
                self.write_expr(cond, false)?;
                w!(self.fn_bodies, "?");
                self.write_expr(then, false)?;
                w!(self.fn_bodies, ":");
                self.write_expr(els, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Cast(inner) => {
                self.type_writer.add_type(expr.ty)?;
                w!(self.fn_bodies, "(({})", self.ctx.get_type(expr.ty));
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Goto(label) => {
                w!(self.fn_bodies, "goto {}", self.ctx.get_name(*label));
            }
            ExprKind::Return(inner) => {
                w!(self.fn_bodies, "return ");
                self.write_expr(inner, false)?;
            }
            ExprKind::Unreachable => {
                w!(self.fn_bodies, "__builtin_unreachable()");
            }
            ExprKind::CodegenIntrinsic(kind) => match kind {
                CodegenIntrinsicKind::SizeOfLike(n, typ) => {
                    self.type_writer.add_type(typ)?;
                    w!(self.fn_bodies, "{}({})", n, self.ctx.get_type(typ));
                }
                CodegenIntrinsicKind::FunctionLike(n) => {
                    w!(self.fn_bodies, "{}", n);
                }
                CodegenIntrinsicKind::ConstLike(n) => {
                    w!(self.fn_bodies, "{}", n);
                }
                CodegenIntrinsicKind::Asm(n) => {
                    w!(self.fn_bodies, "asm volatile({:?})", *n);
                }
            },
            ExprKind::Void => {}
        }

        if bare_block {
            w!(self.fn_bodies, ";");
        }

        Ok(())
    }

    pub fn write_function_decl(
        &mut self,
        id: IrId,
        item: &'ir Function<'ir>,
    ) -> Result<(), AluminaError> {
        let should_export = item.attributes.contains(&Attribute::Export);

        self.type_writer.add_type(item.return_type)?;
        for arg in item.args.iter() {
            self.type_writer.add_type(arg.ty)?;
        }

        if item
            .attributes
            .contains(&Attribute::Codegen(CodegenType::CMain))
        {
            return Ok(());
        }

        if item.body.get().is_none() || should_export {
            self.ctx
                .register_name(id, CName::Native(item.name.unwrap()));
            write_function_signature(self.ctx, &mut self.fn_decls, id, item, false)?;
        } else {
            self.ctx.register_name(
                id,
                CName::Mangled(item.name.unwrap_or("anonymous"), self.ctx.make_id()),
            );
            write_function_signature(
                self.ctx,
                &mut self.fn_decls,
                id,
                item,
                !self.ctx.global_ctx.has_flag("debug"),
            )?;
        }

        w!(self.fn_decls, ";");

        Ok(())
    }

    pub fn write_static_decl(
        &mut self,
        id: IrId,
        item: &'ir Static<'ir>,
    ) -> Result<(), AluminaError> {
        self.type_writer.add_type(item.typ)?;

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

        if !item.typ.is_zero_sized() {
            if item.r#extern {
                w!(
                    self.fn_decls,
                    "\nextern{} {} {};",
                    attributes,
                    self.ctx.get_type(item.typ),
                    self.ctx.get_name(id)
                );
            } else {
                w!(
                    self.fn_decls,
                    "\nstatic{} {} {};",
                    attributes,
                    self.ctx.get_type(item.typ),
                    self.ctx.get_name(id)
                );
            }
        }

        Ok(())
    }

    pub fn write_function_body(
        &mut self,
        id: IrId,
        item: &'ir Function<'ir>,
    ) -> Result<(), AluminaError> {
        let should_export = item.attributes.contains(&Attribute::Export);

        if item.body.get().is_none() {
            return Ok(());
        }

        if item
            .attributes
            .contains(&Attribute::Codegen(CodegenType::CMain))
        {
            // Clang expects an exact signature
            w!(
                self.fn_bodies,
                "int main(int {}, char **{})",
                self.ctx.get_name(item.args[0].id),
                self.ctx.get_name(item.args[1].id)
            );
        } else {
            write_function_signature(
                self.ctx,
                &mut self.fn_bodies,
                id,
                item,
                !should_export && !self.ctx.global_ctx.has_flag("debug"),
            )?;
        }

        let body = item.body.get().unwrap();
        w!(self.fn_bodies, "{{\n");
        self.indent += 2;

        if item.args.iter().any(|a| a.ty.is_never()) {
            // functions that accept a parameter that is of never type can never be legally called,
            // so we add this to keep C compiler from complaining. If someone called it, it's already
            // UB.
            self.write_stmt(&Statement::Expression(&Expr {
                ty: &Ty::Builtin(BuiltinType::Never),
                kind: ExprKind::Unreachable,
                value_type: ValueType::RValue,
                is_const: false,
            }))?;
        } else {
            for def in body.local_defs.iter() {
                self.write_local_def(def)?;
            }
            for stmt in body.statements.iter() {
                self.write_stmt(stmt)?;
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
