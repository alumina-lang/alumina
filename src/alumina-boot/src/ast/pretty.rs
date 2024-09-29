use crate::{ast::StaticForLoopVariable, src::scope::BoundItemType};

use super::{
    AstCtx, BinOp, BuiltinType, ClosureBinding, ExprKind, ExprP, FnKind, Function, Id, Item, ItemP,
    Lit, Statement, StatementKind, Ty, TyP, UnOp,
};
use std::fmt::Write;

pub struct PrettyPrinter<'ast> {
    ast: &'ast AstCtx<'ast>,
}

impl<'ast> PrettyPrinter<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>) -> Self {
        Self { ast }
    }

    pub fn print_stmt(&mut self, stmt: &Statement<'ast>) -> String {
        match &stmt.kind {
            StatementKind::Expression(e) => format!("{};", self.print_expr(e)),
            StatementKind::LetDeclaration(l) => match (l.ty, l.value) {
                (None, None) => format!("let {};", self.id_to_name(l.id)),
                (Some(t), None) => format!("let {}: {};", self.id_to_name(l.id), self.print_ty(t)),
                (None, Some(v)) => {
                    format!("let {} = {};", self.id_to_name(l.id), self.print_expr(v))
                }
                (Some(t), Some(v)) => format!(
                    "let {}: {} = {};",
                    self.id_to_name(l.id),
                    self.print_ty(t),
                    self.print_expr(v)
                ),
            },
        }
    }

    pub fn print_builtin_type(&mut self, kind: BuiltinType) -> String {
        match kind {
            BuiltinType::Never => "!".to_string(),
            BuiltinType::Bool => "bool".to_string(),
            BuiltinType::U8 => "u8".to_string(),
            BuiltinType::U16 => "u16".to_string(),
            BuiltinType::U32 => "u32".to_string(),
            BuiltinType::U64 => "u64".to_string(),
            BuiltinType::U128 => "u128".to_string(),
            BuiltinType::USize => "usize".to_string(),
            BuiltinType::ISize => "isize".to_string(),
            BuiltinType::I8 => "i8".to_string(),
            BuiltinType::I16 => "i16".to_string(),
            BuiltinType::I32 => "i32".to_string(),
            BuiltinType::I64 => "i64".to_string(),
            BuiltinType::I128 => "i128".to_string(),
            BuiltinType::F32 => "f32".to_string(),
            BuiltinType::F64 => "f64".to_string(),
        }
    }

    pub fn print_ty(&mut self, ty: TyP<'ast>) -> String {
        self.print_ty_full(ty, false)
    }

    fn print_string_literal(&mut self, s: &[u8]) -> String {
        let mut out = String::with_capacity(s.len() * 2);
        out.push('"');
        for c in s {
            match c {
                b'\t' => out.push_str("\\t"),
                b'\r' => out.push_str("\\r"),
                b'\\' => out.push_str("\\\\"),
                b'"' => out.push_str("\\\""),
                b'\0' => out.push_str("\\0"),
                b'\n' => out.push_str("\\n"),
                b'\x01'..=b'\x1a' | b'\x80'..=b'\xff' => {
                    out.push_str(&format!("\\x{:02x}", c));
                }
                _ => out.push(*c as char),
            }
        }
        out.push('"');
        out
    }

    fn print_ty_full(&mut self, ty: TyP<'ast>, turbofish: bool) -> String {
        match ty {
            Ty::Tag(tag, inner) => {
                format!("/* {} */ {}", tag, self.print_ty_full(inner, turbofish))
            }
            Ty::Placeholder(id) => self.id_to_name(*id),
            Ty::Item(item) => self.print_item(item, None, false),
            Ty::Builtin(kind) => self.print_builtin_type(*kind),
            Ty::Pointer(inner, is_const) => format!(
                "&{}{}",
                if *is_const { "" } else { "mut " },
                self.print_ty_full(inner, turbofish)
            ),
            Ty::Slice(inner, is_const) => format!(
                "&{}[{}]",
                if *is_const { "" } else { "mut " },
                self.print_ty_full(inner, turbofish)
            ),
            Ty::Dyn(protos, is_const) => {
                let mut s = String::new();
                for (i, proto) in protos.iter().enumerate() {
                    if i != 0 {
                        s.push_str(" + ");
                    }
                    s.push_str(&self.print_ty_full(proto, turbofish));
                }

                if protos.len() > 1 {
                    format!("&{}dyn ({})", if *is_const { "" } else { "mut " }, s)
                } else {
                    format!("&{}dyn {}", if *is_const { "" } else { "mut " }, s)
                }
            }
            Ty::TypeOf(inner) => format!("typeof({})", self.print_expr(inner)),
            Ty::Array(inner, len) => {
                format!(
                    "[{}; {}]",
                    self.print_ty_full(inner, turbofish),
                    self.print_expr(len)
                )
            }
            Ty::Tuple(elems) => {
                let mut s = String::new();
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_ty_full(elem, turbofish));
                }

                format!("({})", s)
            }
            Ty::When(cond, then, els) => format!(
                "when {} {{ {} }} else {{ {} }}",
                self.print_ty_full(then, turbofish),
                self.print_expr(cond),
                self.print_ty_full(els, turbofish)
            ),
            Ty::FunctionPointer(args, ret) => {
                let mut s = String::new();
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_ty_full(arg, turbofish));
                }

                format!("fn({}) -> {}", s, self.print_ty_full(ret, turbofish))
            }
            Ty::FunctionProtocol(args, ret) => {
                let mut s = String::new();
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_ty_full(arg, turbofish));
                }

                format!("Fn({}) -> {}", s, self.print_ty_full(ret, turbofish))
            }
            Ty::Generic(base, args) => {
                let mut s = String::new();
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_ty_full(arg, turbofish));
                }

                if turbofish {
                    format!("{}::<{}>", self.print_ty(base), s)
                } else {
                    format!("{}<{}>", self.print_ty(base), s)
                }
            }
            Ty::EtCetera(inner) => format!("{}...", self.print_ty_full(inner, turbofish)),
            Ty::Deref(inner) => format!("*{}", self.print_ty_full(inner, turbofish)),
            Ty::TupleIndex(inner, idx) => match idx.kind {
                ExprKind::Lit(Lit::Int(false, idx, None | Some(BuiltinType::USize))) => {
                    format!("{}.{}", self.print_ty_full(inner, turbofish), idx)
                }
                _ => format!(
                    "{}.({})",
                    self.print_ty_full(inner, turbofish),
                    self.print_expr(idx)
                ),
            },
            Ty::Defered(spec) => {
                format!("{}::{}", self.print_ty_full(spec.ty, turbofish), spec.name)
            }
        }
    }

    pub fn print_item(
        &mut self,
        item: ItemP<'ast>,
        generic_args: Option<&'ast [TyP<'ast>]>,
        turbofish: bool,
    ) -> String {
        let ret = self.id_to_name(item.id);

        if let Some(generic_args) = generic_args {
            let mut s = String::new();
            for (i, arg) in generic_args.iter().enumerate() {
                if i != 0 {
                    s.push_str(", ");
                }
                s.push_str(&self.print_ty(arg));
            }

            if turbofish {
                format!("{}::<{}>", ret, s)
            } else {
                format!("{}<{}>", ret, s)
            }
        } else {
            ret
        }
    }

    pub fn print_expr(&mut self, expr: ExprP<'ast>) -> String {
        self.print_expr_full(expr, false, false)
    }

    pub fn print_expr_parens(&mut self, expr: ExprP<'ast>) -> String {
        self.print_expr_full(expr, false, true)
    }

    fn id_to_name(&self, id: Id) -> String {
        self.ast
            .local_name(id)
            .map(str::to_string)
            .unwrap_or(id.to_string())
    }

    fn print_lambda(
        &mut self,
        bindings: Option<&'ast [ClosureBinding<'ast>]>,
        func: &Function<'ast>,
    ) -> String {
        let mut s = String::new();
        for binding in bindings.iter().flat_map(|s| s.iter()) {
            if !s.is_empty() {
                s.push_str(", ");
            }
            match binding.binding_type {
                BoundItemType::ByValue => write!(s, "={}", self.id_to_name(binding.id)).unwrap(),
                BoundItemType::ByReference => {
                    write!(s, "&{}", self.id_to_name(binding.id)).unwrap()
                }
            }
        }

        for arg in func.args.iter().skip(bindings.is_some() as usize) {
            if !s.is_empty() {
                s.push_str(", ");
            }
            write!(s, "{}: {}", self.id_to_name(arg.id), self.print_ty(arg.ty)).unwrap();
        }

        let ret = if let Ty::Tuple(&[]) = func.return_type {
            String::new()
        } else {
            format!(" -> {}", self.print_ty(func.return_type))
        };

        format!(
            "|{}|{} {}",
            s,
            ret,
            self.print_expr_full(func.body.unwrap(), true, false)
        )
    }

    fn print_expr_full(&mut self, expr: ExprP<'ast>, braces: bool, need_parens: bool) -> String {
        let mut add_parens = false;

        let ret = match expr.kind {
            ExprKind::Block(stmts, ret) => {
                if stmts.is_empty() {
                    return self.print_expr_full(ret, braces, need_parens);
                }

                let mut s = String::new();
                for stmt in stmts {
                    s.push_str(&self.print_stmt(stmt));
                    s.push(' ');
                }

                // Return to not add extra braces
                if matches!(ret.kind, ExprKind::Void) {
                    return format!("{{ {}}}", s);
                } else {
                    return format!("{{ {}{} }}", s, self.print_expr(ret));
                }
            }
            ExprKind::Binary(op, lhs, rhs) => {
                add_parens = true;
                match op {
                    BinOp::And => format!(
                        "{} && {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Or => format!(
                        "{} || {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::BitAnd => format!(
                        "{} & {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::BitOr => format!(
                        "{} | {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::BitXor => format!(
                        "{} ^ {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Eq => format!(
                        "{} == {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Neq => format!(
                        "{} != {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Lt => format!(
                        "{} < {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::LEq => format!(
                        "{} <= {}",
                        self.print_expr(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Gt => format!(
                        "{} > {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::GEq => format!(
                        "{} >= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::LShift => format!(
                        "{} << {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::RShift => format!(
                        "{} >> {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Plus => format!(
                        "{} + {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Minus => format!(
                        "{} - {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Mul => format!(
                        "{} * {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Div => format!(
                        "{} / {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Mod => format!(
                        "{} % {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                }
            }
            ExprKind::Call(callee, args) => {
                let mut s = String::new();
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_expr(arg));
                }

                format!("{}({})", self.print_expr_parens(callee), s)
            }
            ExprKind::Defered(spec) => {
                format!("{}::{}", self.print_ty(spec.ty), spec.name)
            }

            // TODO: Somehow print macros with bound variables
            ExprKind::Macro(i, _) => self.print_item(i, None, true),
            ExprKind::Fn(ref kind, generic_args) => match kind {
                FnKind::Normal(i) => match i.try_get() {
                    Some(Item::Function(fun)) if fun.is_lambda => self.print_lambda(None, fun),
                    _ => self.print_item(i, generic_args, true),
                },
                FnKind::Closure(bindings, item) => {
                    let fun = item.get_function();
                    self.print_lambda(Some(*bindings), fun)
                }
                FnKind::Defered(spec) => {
                    format!("{}::{}", self.print_ty(spec.ty), spec.name)
                }
            },
            ExprKind::Ref(inner) => {
                add_parens = true;
                format!("&{}", self.print_expr_parens(inner))
            }
            ExprKind::Deref(inner) => {
                add_parens = true;
                format!("*{}", self.print_expr_parens(inner))
            }
            ExprKind::Unary(op, inner) => {
                add_parens = true;
                match op {
                    UnOp::Neg => format!("-{}", self.print_expr_parens(inner)),
                    UnOp::Not => format!("!{}", self.print_expr_parens(inner)),
                    UnOp::BitNot => format!("~{}", self.print_expr_parens(inner)),
                }
            }
            ExprKind::Assign(lhs, rhs) => {
                format!("{} = {}", self.print_expr(lhs), self.print_expr(rhs))
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                add_parens = true;
                match op {
                    BinOp::And => format!(
                        "{} &= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Or => format!(
                        "{} |= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::BitAnd => format!(
                        "{} &= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::BitOr => format!(
                        "{} |= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::BitXor => format!(
                        "{} ^= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::LShift => format!(
                        "{} <<= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::RShift => format!(
                        "{} >>= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Plus => format!(
                        "{} += {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Minus => format!(
                        "{} -= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Mul => format!(
                        "{} *= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Div => format!(
                        "{} /= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    BinOp::Mod => format!(
                        "{} %= {}",
                        self.print_expr_parens(lhs),
                        self.print_expr_parens(rhs)
                    ),
                    _ => unreachable!(),
                }
            }
            ExprKind::Local(id) => self.id_to_name(id),
            ExprKind::StaticFor(loop_var, range, body) => match loop_var {
                StaticForLoopVariable::Single(id) => {
                    format!(
                        "for const {} in {} {}",
                        self.id_to_name(id),
                        self.print_expr(range),
                        self.print_expr_full(body, true, false)
                    )
                }
                StaticForLoopVariable::Tuple(ids) => {
                    let mut s = String::new();
                    for (i, id) in ids.iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&self.id_to_name(*id));
                    }

                    format!(
                        "for const ({}) in {} {}",
                        s,
                        self.print_expr(range),
                        self.print_expr_full(body, true, false)
                    )
                }
            },
            ExprKind::Static(item, generic_args) => self.print_item(item, generic_args, true),
            ExprKind::Const(item, generic_args) => self.print_item(item, generic_args, true),
            ExprKind::EnumValue(item, id) => {
                format!(
                    "{}::{}",
                    self.print_item(item, None, true),
                    self.id_to_name(id)
                )
            }
            ExprKind::Lit(ref lit) => match lit {
                Lit::Str(s) => self.print_string_literal(s),
                Lit::Int(sign, val, ty) => {
                    let mut s = String::new();
                    if *sign {
                        s.push('-');
                    }
                    s.push_str(&val.to_string());
                    if let Some(kind) = ty {
                        s.push_str(&self.print_builtin_type(*kind));
                    }
                    s
                }
                Lit::Float(val, kind) => {
                    let mut s = String::new();
                    write!(s, "{}", val).unwrap();
                    if let Some(kind) = kind {
                        s.push_str(&self.print_builtin_type(*kind));
                    }
                    s
                }
                Lit::Bool(v) => format!("{}", v),
                Lit::Null => "null".to_string(),
            },
            ExprKind::Loop(body) => format!("loop {}", self.print_expr_full(body, true, false)),
            ExprKind::Break(val) => {
                if let Some(val) = val {
                    add_parens = true;
                    format!("break {}", self.print_expr_parens(val))
                } else {
                    "break".to_string()
                }
            }
            ExprKind::Return(val) => {
                if let Some(val) = val {
                    add_parens = true;
                    format!("return {}", self.print_expr_parens(val))
                } else {
                    "return".to_string()
                }
            }
            ExprKind::Yield(val) => {
                if let Some(val) = val {
                    add_parens = true;
                    format!("yield {}", self.print_expr_parens(val))
                } else {
                    "yield".to_string()
                }
            }
            ExprKind::Defer(val) => {
                add_parens = true;
                format!("defer {}", self.print_expr_parens(val))
            }
            ExprKind::Continue => "continue".to_string(),
            ExprKind::Tuple(args) => {
                let mut s = String::new();
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_expr(arg));
                }
                format!("({})", s)
            }
            ExprKind::Array(elems) => {
                let mut s = String::new();
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&self.print_expr(elem));
                }
                format!("[{}]", s)
            }
            ExprKind::Struct(ty, initializers) => {
                let mut s = String::new();
                for (i, field) in initializers.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&format!("{}: {}", field.name, self.print_expr(field.value)));
                }
                format!("{} {{ {} }}", self.print_ty_full(ty, true), s)
            }
            ExprKind::BoundParam(_, id, _) => self.id_to_name(id),
            ExprKind::Field(base, field, _, generic_args) => {
                if let Some(args) = generic_args {
                    let mut s = String::new();
                    for (i, arg) in args.iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&self.print_ty(arg));
                    }

                    format!("{}.{}::<{}>", self.print_expr(base), s, field)
                } else {
                    format!("{}.{}", self.print_expr(base), field)
                }
            }
            ExprKind::TupleIndex(base, idx) => match idx.kind {
                ExprKind::Lit(Lit::Int(false, idx, None | Some(BuiltinType::USize))) => {
                    format!("{}.{}", self.print_expr(base), idx)
                }
                _ => format!("{}.({})", self.print_expr(base), self.print_expr(idx)),
            },
            ExprKind::Index(base, idx) => {
                format!("{}[{}]", self.print_expr_parens(base), self.print_expr(idx))
            }
            ExprKind::Range(lower, upper, inclusive) => {
                add_parens = true;
                match (lower, upper) {
                    (Some(lower), Some(upper)) => {
                        if inclusive {
                            format!(
                                "{}..={}",
                                self.print_expr_parens(lower),
                                self.print_expr_parens(upper)
                            )
                        } else {
                            format!(
                                "{}..{}",
                                self.print_expr_parens(lower),
                                self.print_expr_parens(upper)
                            )
                        }
                    }
                    (Some(lower), None) => format!("{}..", self.print_expr_parens(lower)),
                    (None, Some(upper)) => {
                        if inclusive {
                            format!("..={}", self.print_expr_parens(upper))
                        } else {
                            format!("..{}", self.print_expr_parens(upper))
                        }
                    }
                    (None, None) => "..".to_string(),
                }
            }
            ExprKind::TypeCheck(inner, ty) => {
                add_parens = true;
                format!("{} is {}", self.print_expr_parens(inner), self.print_ty(ty))
            }
            ExprKind::If(cond, then, els) | ExprKind::StaticIf(cond, then, els) => {
                add_parens = true;

                let kw = match expr.kind {
                    ExprKind::If(_, _, _) => "if",
                    ExprKind::StaticIf(_, _, _) => "when",
                    _ => unreachable!(),
                };

                if matches!(els.kind, ExprKind::Void) {
                    return format!(
                        "{} {} {}",
                        kw,
                        self.print_expr(cond),
                        self.print_expr_full(then, true, false)
                    );
                } else {
                    format!(
                        "{} {} {} else {}",
                        kw,
                        self.print_expr(cond),
                        self.print_expr_full(then, true, false),
                        self.print_expr_full(els, true, false)
                    )
                }
            }
            ExprKind::Cast(inner, ty) => {
                add_parens = true;
                format!("{} as {}", self.print_expr_parens(inner), self.print_ty(ty))
            }
            ExprKind::Void => {
                if braces {
                    return "{}".to_string();
                } else {
                    "()".to_string()
                }
            }
            ExprKind::EtCetera(inner) => format!("{}...", self.print_expr_parens(inner)),
            // Those will never appear in the AST post-macro expansion
            ExprKind::EtCeteraMacro(_) | ExprKind::MacroInvocation(_, _) => unreachable!(),
            ExprKind::Tag(tag, inner) => format!("/* {} */ {}", tag, self.print_expr(inner)),
        };

        if braces {
            format!("{{ {} }}", ret)
        } else if need_parens && add_parens {
            format!("({})", ret)
        } else {
            ret
        }
    }
}
