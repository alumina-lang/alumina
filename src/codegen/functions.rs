use crate::{
    ast::{Attribute, BinOp, UnOp},
    codegen::CName,
    common::AluminaErrorKind,
    ir::{const_eval::Value, ExprKind, ExprP, Function, IrId, Statement, Ty},
};

use super::{types::TypeWriter, w, CodegenCtx};

use std::fmt::Write;

pub struct FunctionWriter<'ir, 'gen> {
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    type_writer: &'gen TypeWriter<'ir, 'gen>,
    fn_decls: String,
    fn_bodies: String,
    indent: usize,
}

pub fn write_function_signature<'ir, 'gen>(
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    buf: &mut String,
    id: IrId,
    item: &'ir Function<'ir>,
    is_static: bool,
) -> Result<(), AluminaErrorKind> {
    let name = ctx.get_name(id);

    let mut attributes = if item.attributes.contains(&Attribute::ForceInline) {
        "__attribute__((always_inline)) inline ".to_string()
    } else {
        "".to_string()
    };

    if item.return_type.is_never() {
        attributes = format!("_Noreturn {}", attributes);
    }

    if is_static {
        w!(
            buf,
            "\n{}static {} {}(",
            attributes,
            ctx.get_type(item.return_type),
            name
        );
    } else {
        w!(
            buf,
            "\n{}{} {}(",
            attributes,
            ctx.get_type(item.return_type),
            name
        );
    }
    for (idx, arg) in item.args.iter().enumerate() {
        let name = ctx.get_name(arg.id);
        if idx > 0 {
            w!(buf, ", ");
        }
        w!(buf, "{} {}", ctx.get_type(arg.ty), name);
    }

    w!(buf, ")");
    Ok(())
}

impl<'ir, 'gen> FunctionWriter<'ir, 'gen> {
    pub fn new(ctx: &'gen CodegenCtx<'ir, 'gen>, type_writer: &'gen TypeWriter<'ir, 'gen>) -> Self {
        Self {
            ctx,
            type_writer,
            fn_decls: String::with_capacity(10 * 1024),
            fn_bodies: String::with_capacity(10 * 1024),
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
            Value::U32(val) => w!(self.fn_bodies, "{}", val),
            Value::U64(val) => w!(self.fn_bodies, "{}", val),
            Value::U128(val) => w!(self.fn_bodies, "{}", val),
            Value::I8(val) => w!(self.fn_bodies, "{}", val),
            Value::I16(val) => w!(self.fn_bodies, "{}", val),
            Value::I32(val) => w!(self.fn_bodies, "{}", val),
            Value::I64(val) => w!(self.fn_bodies, "{}", val),
            Value::I128(val) => w!(self.fn_bodies, "{}", val),
            Value::USize(val) => w!(self.fn_bodies, "{}", val),
            Value::ISize(val) => w!(self.fn_bodies, "{}", val),
            _ => unimplemented!(),
        }
    }

    fn indent(&mut self) {
        w!(self.fn_bodies, "{}", " ".repeat(self.indent));
    }

    pub fn write_stmt(&mut self, stmt: &Statement<'ir>) -> Result<(), AluminaErrorKind> {
        match stmt {
            Statement::Expression(e) => {
                if !(e.is_void() && e.is_unreachable()) {
                    self.indent();
                    self.write_expr(e, false)?;
                    w!(self.fn_bodies, ";\n");
                }
            }
            Statement::LocalDef(id, typ) => {
                self.type_writer.add_type(typ)?;
                self.indent();
                w!(
                    self.fn_bodies,
                    "{} {};\n",
                    self.ctx.get_type(typ),
                    self.ctx.get_name(*id)
                );
            }
            Statement::Label(id) => {
                self.indent();
                w!(self.fn_bodies, "{}: ;\n", self.ctx.get_name(*id));
            }
        }

        Ok(())
    }

    pub fn write_expr(
        &mut self,
        expr: ExprP<'ir>,
        bare_block: bool,
    ) -> Result<(), AluminaErrorKind> {
        self.type_writer.add_type(expr.ty)?;

        if bare_block {
            self.indent();
        }

        match expr.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                w!(self.fn_bodies, "(");
                self.write_expr(lhs, false)?;
                self.write_binop(op);
                self.write_expr(rhs, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                self.write_expr(lhs, false)?;
                self.write_binop(op);
                w!(self.fn_bodies, "=");
                self.write_expr(rhs, false)?;
            }
            ExprKind::Call(callee, args) => {
                self.write_expr(callee, false)?;
                w!(self.fn_bodies, "(");
                for (idx, arg) in args.iter().enumerate() {
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
                self.write_unop(op);
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
                w!(self.fn_bodies, "{}", self.ctx.get_name(id));
            }
            ExprKind::Lit(ref l) => match l {
                crate::ir::Lit::Str(v) => {
                    w!(self.fn_bodies, "((const uint8_t[{}]){{", v.len());
                    for (idx, c) in v.iter().enumerate() {
                        if idx > 0 {
                            w!(self.fn_bodies, ", ");
                        }
                        w!(self.fn_bodies, "{:#04x}", *c as u8);
                    }
                    w!(self.fn_bodies, "}})");
                }
                crate::ir::Lit::Int(v) => {
                    w!(self.fn_bodies, "(({}){})", self.ctx.get_type(expr.ty), v);
                }
                crate::ir::Lit::Float(_) => todo!(),
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
                    w!(self.fn_bodies, "(({})0)", self.ctx.get_type(expr.ty));
                }
            },
            ExprKind::Block(stmts, ret) => {
                if bare_block {
                    for stmt in stmts {
                        self.write_stmt(stmt)?;
                    }

                    if !ret.is_void() {
                        self.write_expr(ret, true)?;
                    }
                } else {
                    w!(self.fn_bodies, "({{\n");
                    self.indent += 2;
                    for stmt in stmts {
                        self.write_stmt(stmt)?;
                    }

                    if !(ret.is_void() && ret.is_unreachable()) {
                        self.write_expr(ret, false)?;
                        w!(self.fn_bodies, ";");
                    }

                    self.indent -= 2;

                    w!(self.fn_bodies, "}})");
                }
            }
            ExprKind::ConstValue(v) => {
                w!(self.fn_bodies, "(({})", self.ctx.get_type(expr.ty));
                self.write_const_val(v);
                w!(self.fn_bodies, ")");
            }
            ExprKind::Field(inner, field) => {
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ".{}", self.ctx.get_name(field));
            }
            ExprKind::TupleIndex(inner, idx) => {
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, "._{}", idx);
            }
            ExprKind::If(cond, then, els) if expr.ty.is_void() || expr.diverges() => {
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
                w!(self.fn_bodies, "(({})", self.ctx.get_type(expr.ty));
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Goto(label) => {
                w!(self.fn_bodies, "goto {}", self.ctx.get_name(label));
            }
            ExprKind::Return(inner) => {
                w!(self.fn_bodies, "return ");
                self.write_expr(inner, false)?;
            }
            ExprKind::Unreachable => {}
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
    ) -> Result<(), AluminaErrorKind> {
        let should_export = item.attributes.contains(&Attribute::Export);

        self.type_writer.add_type(item.return_type)?;
        for arg in item.args.iter() {
            self.type_writer.add_type(arg.ty)?;
        }

        if item.body.is_empty() || should_export {
            self.ctx
                .register_name(id, CName::Native(item.name.unwrap()));
            write_function_signature(self.ctx, &mut self.fn_decls, id, item, false)?;
        } else {
            self.ctx.register_name(
                id,
                CName::Mangled(item.name.unwrap_or("anonymous"), self.ctx.make_id()),
            );
            write_function_signature(self.ctx, &mut self.fn_decls, id, item, true)?;
        }

        w!(self.fn_decls, ";");

        Ok(())
    }

    pub fn write_function_body(
        &mut self,
        id: IrId,
        item: &'ir Function<'ir>,
    ) -> Result<(), AluminaErrorKind> {
        let should_export = item.attributes.contains(&Attribute::Export);

        if item.body.is_empty() {
            return Ok(());
        }

        write_function_signature(self.ctx, &mut self.fn_bodies, id, item, !should_export)?;

        let body = item.body.get();
        w!(self.fn_bodies, "{{\n");
        self.indent += 2;
        for stmt in body.iter() {
            self.write_stmt(stmt)?;
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
