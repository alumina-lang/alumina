//pub mod types;

use std::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    fmt::{Display, Write},
    marker::PhantomData,
    rc::Rc,
};

use crate::{
    ast::{BinOp, UnOp, Attribute, AttributeKind},
    common::Incrementable,
    ir::{ExprKind, ExprP, Function, Statement},
};
use bumpalo::Bump;
use once_cell::unsync::OnceCell;

use crate::{
    ast::BuiltinType,
    common::AluminaError,
    ir::{IRItem, IRItemP, IrId, Struct, Ty, TyP},
};

#[derive(Debug)]
struct Decl {
    name: String,
}

fn is_elided(ty: &Ty<'_>) -> bool {
    *ty == Ty::Builtin(BuiltinType::Void) || *ty == Ty::Builtin(BuiltinType::Never)
}

pub struct CCodegen<'ir, 'cod> {
    type_decls: String,
    type_bodies: String,
    fn_decls: String,
    fn_bodies: String,

    indent: usize,

    decl_map: HashMap<TyP<'ir>, Rc<OnceCell<CName>>>,
    body_map: HashSet<TyP<'ir>>,
    needs_body: HashSet<TyP<'ir>>,
    id_map: RefCell<HashMap<IrId, CName>>,
    counter: Cell<usize>,
    _phantom: PhantomData<&'cod ()>,
}

macro_rules! w {
    ($buf:expr, $($arg:tt)*) => (
        write!($buf, $($arg)*).unwrap()
    );
}

#[derive(Clone, Debug)]
pub enum CName {
    Native(String),
    Id(usize),
    Mangled(String, String),
}

impl CName {
    pub fn from_native(name: &str) -> Self {
        Self::Native(name.to_string())
    }

    fn pointer(self, is_const: bool) -> CName {
        use CName::*;
        let suf = if is_const { "cp" } else { "p" };

        match self {
            Native(name) => Mangled(name, suf.to_string()),
            Mangled(name, mut suffix) => {
                suffix.push_str(suf);
                Mangled(name, suffix)
            }
            Id(i) => Mangled(format!("al{}", i), suf.to_string()),
        }
    }

    fn array(self, size: usize) -> CName {
        use CName::*;
        match self {
            Native(name) => Mangled(name, format!("A{}", size)),
            Mangled(name, mut suffix) => {
                write!(&mut suffix, "A{}", size).unwrap();
                Mangled(name, suffix)
            }
            Id(i) => Mangled(format!("al{}", i), format!("A{}", size)),
        }
    }
}



impl Display for CName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CName::*;
        match self {
            Native(name) => write!(f, "{}", name),
            Mangled(name, suffix) => {
                write!(
                    f,
                    "{}_{}",
                    name.replace("_", "__"),
                    suffix.replace("_", "__")
                )
            }
            Id(i) => write!(f, "al{}", i),
        }
    }
}

impl<'ir, 'cod> CCodegen<'ir, 'cod> {
    pub fn new() -> Self {
        let mut result = Self {
            type_decls: String::with_capacity(10 * 1024),
            type_bodies: String::with_capacity(10 * 1024),
            fn_decls: String::with_capacity(10 * 1024),
            fn_bodies: String::with_capacity(10 * 1024),
            indent: 0,
            decl_map: HashMap::new(),
            body_map: HashSet::new(),
            needs_body: HashSet::new(),
            id_map: RefCell::new(HashMap::new()),
            counter: Cell::new(0),
            _phantom: PhantomData,
        };

        result.write_prelude();
        result
    }

    fn write_prelude(&mut self) {
        writeln!(self.type_decls, "#include <stdint.h>").unwrap();
        writeln!(self.type_decls, "#include <stddef.h>").unwrap();
    }

    fn ir_name(&self, id: IrId, provided_name: Option<&'ir str>) -> CName {
        self.id_map
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| {
                provided_name
                    .map(|name| CName::Native(name.to_string()))
                    .unwrap_or(CName::Id(self.counter.increment()))
            })
            .clone()
    }

    fn ty_name(&self, ty: TyP<'ir>) -> CName {
        self.decl_map.get(ty).unwrap().get().unwrap().clone()
    }

    fn ensure_ty(&mut self, ty: TyP<'ir>, ref_only: bool) -> Result<(), AluminaError> {
        if let Ty::Fn(_, _) = ty {
            return Ok(());
        }

        let (cell, body_only) = match self.decl_map.entry(ty) {
            Entry::Occupied(e) => {
                let cell = e.get();
                match cell.get() {
                    Some(n) => {
                        if !ref_only && !self.needs_body.contains(ty) {
                            (cell.clone(), true)
                        } else {
                            return Ok(());
                        }
                    }
                    None => return Err(AluminaError::CycleDetected),
                }
            }
            Entry::Vacant(v) => {
                let item = Rc::new(OnceCell::new());
                (v.insert(item).clone(), false)
            }
        };

        match ty {
            Ty::Builtin(a) if !body_only => {
                let name = CName::from_native(match a {
                    BuiltinType::U8 => "uint8_t",
                    BuiltinType::U16 => "uint16_t",
                    BuiltinType::U32 => "uint32_t",
                    BuiltinType::U64 => "uint64_t",
                    BuiltinType::I8 => "int8_t",
                    BuiltinType::I16 => "int16_t",
                    BuiltinType::I32 => "int32_t",
                    BuiltinType::I64 => "int64_t",
                    BuiltinType::F32 => "float",
                    BuiltinType::F64 => "double",
                    BuiltinType::USize => "size_t",
                    BuiltinType::ISize => "ptrdiff_t",
                    BuiltinType::Bool => "_Bool",
                    BuiltinType::Void => "void",
                    BuiltinType::Never => "void",
                    _ => todo!(),
                });

                cell.set(name).unwrap();
            }
            Ty::Pointer(inner, is_const) if !body_only => {
                self.ensure_ty(inner, true)?;

                let inner = self.ty_name(inner);
                let name = inner.clone().pointer(*is_const);

                if *is_const {
                    w!(self.type_decls, "typedef const {} *{};\n", inner, name);
                } else {
                    w!(self.type_decls, "typedef {} *{};\n", inner, name);
                }

                cell.set(name).unwrap();
            }
            Ty::Array(inner, len) if !body_only => {
                self.ensure_ty(inner, false)?;
                let name = self.ty_name(inner).array(*len);

                w!(self.type_decls, "typedef struct {0} {0};\n", name);
                cell.set(name).unwrap();

                self.needs_body.insert(ty);
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    if !body_only {
                        let name = CName::Id(self.counter.increment());
                        w!(self.type_decls, "typedef struct {0} {0};\n", name);
                        cell.set(name).unwrap();
                    }

                    if !ref_only {
                        self.needs_body.insert(ty);
                        for field in s.fields {
                            self.ensure_ty(field.ty, false)?;
                        }
                    }
                }
                _ => {}
            },
            Ty::Tuple(items) if !body_only => {
                for elem in items.iter() {
                    self.ensure_ty(elem, false)?;
                }

                let name = CName::Id(self.counter.increment());
                w!(self.type_decls, "typedef struct {0} {0};\n", name);

                cell.set(name).unwrap();
                self.needs_body.insert(ty);
            }
            _ => {}
        };

        Ok(())
    }

    fn write_body(&mut self, ty: TyP<'ir>) -> Result<(), AluminaError> {
        if self.body_map.contains(&ty) {
            return Ok(());
        }

        match ty {
            Ty::Array(a, len) => {
                let name = self.ty_name(ty);
                let inner = self.ty_name(a);

                self.write_body(a)?;

                w!(self.type_bodies, "struct {} {{\n", name);
                w!(self.type_bodies, "  {} __data[{}];\n", inner, len);
                w!(self.type_bodies, "}};\n");
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    let name = self.ty_name(ty);

                    for f in s.fields {
                        self.write_body(f.ty)?;
                    }

                    w!(self.type_bodies, "struct {} {{\n", name);
                    for f in s.fields {
                        w!(
                            self.type_bodies,
                            "  {} {};\n",
                            self.ty_name(f.ty),
                            self.ir_name(f.id, None)
                        );
                    }
                    w!(self.type_bodies, "}};\n");
                }
                _ => todo!(),
            },
            Ty::Tuple(items) => {
                let name = self.ty_name(ty);

                for f in items.iter() {
                    self.write_body(f)?;
                }

                w!(self.type_bodies, "struct {} {{\n", name);
                for (idx, f) in items.iter().enumerate() {
                    w!(self.type_bodies, "  {} _{};\n", self.ty_name(f), idx);
                }
                w!(self.type_bodies, "}};\n");
            }
            _ => (),
        };

        self.body_map.insert(ty);

        Ok(())
    }

    pub fn write_function_decl(
        &mut self,
        id: IrId,
        item: &'ir Function<'ir>,
        is_static: bool,
    ) -> Result<(), AluminaError> {
        let name = self.ir_name(id, None);
        self.ensure_ty(item.return_type, false)?;

        if is_static {
            w!(
                self.fn_decls,
                "\nstatic {} {}(",
                self.ty_name(item.return_type),
                name
            );
        } else {
            w!(
                self.fn_decls,
                "\n{} {}(",
                self.ty_name(item.return_type),
                name
            );
        }
        for (idx, arg) in item.args.iter().enumerate() {
            let name = self.ir_name(arg.id, None);
            self.ensure_ty(arg.ty, false)?;

            if idx > 0 {
                w!(self.fn_decls, ", ");
            }
            w!(self.fn_decls, "{} {}", self.ty_name(arg.ty), name);
        }
        w!(self.fn_decls, ");\n");

        Ok(())
    }

    pub fn write_binop(&mut self, op: BinOp) {
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

    pub fn write_unop(&mut self, op: UnOp) {
        match op {
            UnOp::Neg => w!(self.fn_bodies, "-"),
            UnOp::Not => w!(self.fn_bodies, "!"),
            UnOp::BitNot => w!(self.fn_bodies, "~"),
        }
    }

    fn indent(&mut self) {
        w!(self.fn_bodies, "{}", " ".repeat(self.indent));
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
            Statement::LocalDef(id, typ) => {
                self.ensure_ty(typ, false)?;
                self.indent();
                w!(
                    self.fn_bodies,
                    "{} {};\n",
                    self.ty_name(typ),
                    self.ir_name(*id, None)
                );
            }
            Statement::Label(id) => {
                self.indent();
                w!(self.fn_bodies, "{}: ;\n", self.ir_name(*id, None));
            }
            Statement::Goto(id) => {
                self.indent();
                w!(self.fn_bodies, "goto {};\n", self.ir_name(*id, None));
            }
        }

        Ok(())
    }

    pub fn write_expr(&mut self, expr: ExprP<'ir>, bare_block: bool) -> Result<(), AluminaError> {
        self.ensure_ty(expr.typ, false)?;

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
                w!(self.fn_bodies, "{}", self.ir_name(fun.id, None));
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
            ExprKind::Return(inner) => {
                w!(self.fn_bodies, "return ");
                self.write_expr(inner, false)?;
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
                if let Ty::Array(_, _) = lhs.typ {
                    w!(self.fn_bodies, ".__data");
                }
                w!(self.fn_bodies, "[");
                self.write_expr(rhs, false)?;
                w!(self.fn_bodies, "]");
            }
            ExprKind::Local(id) => {
                w!(self.fn_bodies, "{}", self.ir_name(id, None));
            }
            ExprKind::Lit(ref l) => match l {
                crate::ir::Lit::Str(_) => todo!(),
                crate::ir::Lit::Int(v) => {
                    w!(self.fn_bodies, "(({}){})", self.ty_name(expr.typ), v);
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
                    w!(self.fn_bodies, "(({})0)", self.ty_name(expr.typ));
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

                    self.write_expr(ret, false)?;
                    w!(self.fn_bodies, ";");

                    self.indent -= 2;

                    w!(self.fn_bodies, "}})");
                }
            }
            ExprKind::ConstValue(_) => todo!(),
            ExprKind::Field(inner, field) => {
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ".{}", self.ir_name(field, None));
            }
            ExprKind::TupleIndex(inner, idx) => {
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, "._{}", idx);
            }
            ExprKind::If(cond, then, els) if expr.typ.is_void() => {
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
                w!(self.fn_bodies, "(({})", self.ty_name(expr.typ));
                self.write_expr(inner, false)?;
                w!(self.fn_bodies, ")");
            }
            ExprKind::Unreachable => {}
            ExprKind::Void => {}
        }

        if bare_block {
            w!(self.fn_bodies, ";");
        }

        Ok(())
    }

    pub fn write_function_body(
        &mut self,
        id: IrId,
        item: &'ir Function<'ir>,
        is_static: bool,
    ) -> Result<(), AluminaError> {
        let name = self.ir_name(id, None);
        self.ensure_ty(item.return_type, false)?;

        if is_static {
            w!(
                self.fn_bodies,
                "\nstatic {} {}(",
                self.ty_name(item.return_type),
                name
            );
        } else {
            w!(
                self.fn_bodies,
                "\n{} {}(",
                self.ty_name(item.return_type),
                name
            );
        }
        
        for (idx, arg) in item.args.iter().enumerate() {
            let name = self.ir_name(arg.id, None);
            self.ensure_ty(arg.ty, false)?;

            if idx > 0 {
                w!(self.fn_bodies, ", ");
            }
            w!(self.fn_bodies, "{} {}", self.ty_name(arg.ty), name);
        }
        w!(self.fn_bodies, ") {{\n");

        let body = item.body.get();
        self.indent += 2;
        for stmt in body.iter() {
            self.write_stmt(stmt)?;
        }
        self.indent -= 2;
        w!(self.fn_bodies, "}}\n");

        Ok(())
    }

    pub fn write_item(&mut self, item: IRItemP<'ir>) -> Result<(), AluminaError> {
        match item.get() {
            IRItem::Function(fun) => {
                let mut exported = fun.body.is_empty();
                for attribute in fun.attributes.iter() {
                    match attribute.kind {
                        AttributeKind::Export => {
                            exported = true;
                        }
                    }
                }
                if exported {
                    self.ir_name(item.id, fun.name);
                }
            
                self.write_function_decl(item.id, fun, !exported)?;

                if !fun.body.is_empty() {
                    self.write_function_body(item.id, fun, !exported)?;
                }
            }
            IRItem::Enum(ty) => {
                self.ensure_ty(ty.underlying_type, false)?;
            }
            _ => {}
        }

        Ok(())
    }

    pub fn generate(mut self) -> String {
        let needs_body = self.needs_body.clone();
        for ty in needs_body {
            self.write_body(ty).unwrap();
        }

        let mut buf = String::with_capacity(
            self.type_decls.len()
                + self.type_bodies.len()
                + self.fn_decls.len()
                + self.fn_bodies.len(),
        );

        buf.push_str(&self.type_decls);
        buf.push_str(&self.type_bodies);
        buf.push_str(&self.fn_decls);
        buf.push_str(&self.fn_bodies);

        buf
    }
}
