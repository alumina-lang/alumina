#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;

use clap::Parser;
use rustc_driver::{Compilation, run_compiler};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::mir::ConstValue;
use rustc_middle::ty::TyCtxt;

struct AluDumper {
    output: Box<dyn Write + Send>,
}

/// Names that conflict between value and type namespaces get renamed with _t suffix.
/// This map holds: original_name -> renamed_name for types that need renaming.
type Renames = HashMap<String, String>;

/// Build the set of all type names as they appear in the output (after renaming).
fn build_all_type_names(type_names: &HashSet<String>, renames: &Renames) -> HashSet<String> {
    type_names
        .iter()
        .map(|n| resolve_name(n, renames))
        .collect()
}

/// First pass: collect all names to detect conflicts.
fn collect_names(
    tcx: TyCtxt<'_>,
    seen: &mut HashSet<DefId>,
    item: &rustc_hir::Item,
    value_names: &mut HashSet<String>,
    type_names: &mut HashSet<String>,
) {
    use rustc_hir::ItemKind;
    match &item.kind {
        ItemKind::Mod(_ident, module) => {
            for &item_id in module.item_ids {
                let child = tcx.hir_item(item_id);
                collect_names(tcx, seen, child, value_names, type_names);
            }
        }
        ItemKind::ForeignMod { abi: _, items } => {
            for &foreign_item_id in *items {
                let foreign_item = tcx.hir_foreign_item(foreign_item_id);
                let def_id = foreign_item.owner_id.def_id.to_def_id();
                if seen.insert(def_id) {
                    match &foreign_item.kind {
                        rustc_hir::ForeignItemKind::Fn(..) => {
                            value_names.insert(foreign_item.ident.as_str().to_string());
                        }
                        rustc_hir::ForeignItemKind::Static(..) => {
                            value_names.insert(foreign_item.ident.as_str().to_string());
                        }
                        rustc_hir::ForeignItemKind::Type => {
                            type_names.insert(foreign_item.ident.as_str().to_string());
                        }
                    }
                }
            }
        }
        _ => {
            let def_id = item.owner_id.def_id.to_def_id();
            if !seen.insert(def_id) {
                return;
            }
            match &item.kind {
                ItemKind::TyAlias(ident, ..) => {
                    type_names.insert(ident.as_str().to_string());
                }
                ItemKind::Struct(ident, ..) => {
                    if ident.as_str() != "Padding" {
                        type_names.insert(ident.as_str().to_string());
                    }
                }
                ItemKind::Union(ident, ..) => {
                    type_names.insert(ident.as_str().to_string());
                }
                ItemKind::Enum(ident, _, enum_def) => {
                    if enum_def.variants.is_empty() {
                        type_names.insert(ident.as_str().to_string());
                    }
                }
                ItemKind::Const(ident, ..) => {
                    value_names.insert(ident.as_str().to_string());
                }
                ItemKind::Fn { ident, .. } => {
                    value_names.insert(ident.as_str().to_string());
                }
                _ => {}
            }
        }
    }
}

/// Build rename map: for each type name that conflicts with a value name, rename to name_t.
fn build_renames(value_names: &HashSet<String>, type_names: &HashSet<String>) -> Renames {
    let mut renames = HashMap::new();
    for name in type_names {
        if value_names.contains(name) {
            renames.insert(name.clone(), format!("{}_t", name));
        }
    }
    renames
}

/// Resolve a type name, applying renames if needed.
fn resolve_name(name: &str, renames: &Renames) -> String {
    if let Some(renamed) = renames.get(name) {
        renamed.clone()
    } else {
        name.to_string()
    }
}

/// Format a HIR type as .alu syntax.
fn format_ty(tcx: TyCtxt<'_>, renames: &Renames, ty: &rustc_hir::Ty) -> String {
    use rustc_hir::TyKind;
    match &ty.kind {
        TyKind::Ptr(mt) | TyKind::Ref(_, mt) => {
            let inner = format_ty(tcx, renames, mt.ty);
            match mt.mutbl {
                rustc_hir::Mutability::Mut => format!("&mut {}", inner),
                rustc_hir::Mutability::Not => format!("&{}", inner),
            }
        }
        TyKind::Slice(inner) => format!("[{}]", format_ty(tcx, renames, inner)),
        TyKind::Array(inner, len) => {
            let inner_str = format_ty(tcx, renames, inner);
            let len_str = format_const_arg(tcx, renames, len);
            format!("[{}; {}]", inner_str, len_str)
        }
        TyKind::FnPtr(fn_ptr_ty) => {
            let decl = fn_ptr_ty.decl;
            let params: Vec<String> = decl.inputs.iter().map(|t| format_ty(tcx, renames, t)).collect();
            let ret = format_fn_ret(tcx, renames, &decl.output);
            format!("fn({}){}", params.join(", "), ret)
        }
        TyKind::Never => "!".to_string(),
        TyKind::Tup(tys) if tys.is_empty() => "()".to_string(),
        TyKind::Tup(tys) => {
            let parts: Vec<String> = tys.iter().map(|t| format_ty(tcx, renames, t)).collect();
            format!("({})", parts.join(", "))
        }
        TyKind::Path(qpath) => format_qpath(tcx, renames, qpath, false),
        _ => "/* unknown type */".to_string(),
    }
}

/// Format a Ty<'_, AmbigArg> (from generic args in path segments).
fn format_ambig_ty(tcx: TyCtxt<'_>, renames: &Renames, ty: &rustc_hir::Ty<'_, rustc_hir::AmbigArg>) -> String {
    use rustc_hir::TyKind;
    match &ty.kind {
        TyKind::Ptr(mt) | TyKind::Ref(_, mt) => {
            let inner = format_ty(tcx, renames, mt.ty);
            match mt.mutbl {
                rustc_hir::Mutability::Mut => format!("&mut {}", inner),
                rustc_hir::Mutability::Not => format!("&{}", inner),
            }
        }
        TyKind::Slice(inner) => format!("[{}]", format_ty(tcx, renames, inner)),
        TyKind::Array(inner, len) => {
            let inner_str = format_ty(tcx, renames, inner);
            let len_str = format_const_arg(tcx, renames, len);
            format!("[{}; {}]", inner_str, len_str)
        }
        TyKind::FnPtr(fn_ptr_ty) => {
            let decl = fn_ptr_ty.decl;
            let params: Vec<String> = decl.inputs.iter().map(|t| format_ty(tcx, renames, t)).collect();
            let ret = format_fn_ret(tcx, renames, &decl.output);
            format!("fn({}){}", params.join(", "), ret)
        }
        TyKind::Never => "!".to_string(),
        TyKind::Tup(tys) if tys.is_empty() => "()".to_string(),
        TyKind::Tup(tys) => {
            let parts: Vec<String> = tys.iter().map(|t| format_ty(tcx, renames, t)).collect();
            format!("({})", parts.join(", "))
        }
        TyKind::Path(qpath) => format_qpath(tcx, renames, qpath, false),
        _ => "/* unknown type */".to_string(),
    }
}

/// Format generic args from a path segment (e.g., `<T, U>`).
/// If `turbofish` is true, uses `::<T>` syntax (for expressions); otherwise `<T>` (for types).
fn format_segment_generic_args(
    tcx: TyCtxt<'_>,
    renames: &Renames,
    seg: &rustc_hir::PathSegment,
    turbofish: bool,
) -> String {
    if let Some(args) = seg.args {
        let type_args: Vec<String> = args
            .args
            .iter()
            .filter_map(|arg| {
                if let rustc_hir::GenericArg::Type(ty) = arg {
                    Some(format_ambig_ty(tcx, renames, ty))
                } else {
                    None
                }
            })
            .collect();
        if !type_args.is_empty() {
            return if turbofish {
                format!("::<{}>", type_args.join(", "))
            } else {
                format!("<{}>", type_args.join(", "))
            };
        }
    }
    String::new()
}

/// Format a QPath to get the type/value name.
/// `turbofish`: if true, generic args use `::<T>` syntax (expression context).
fn format_qpath(
    tcx: TyCtxt<'_>,
    renames: &Renames,
    qpath: &rustc_hir::QPath,
    turbofish: bool,
) -> String {
    match qpath {
        rustc_hir::QPath::Resolved(_, path) => {
            if let Some(seg) = path.segments.last() {
                let name = seg.ident.as_str();
                // Padding<T> / MaybeUninit<T> / Option<T> → just T
                // (Option only wraps fn ptrs in libc; Alumina fn ptrs are nullable)
                if name == "Padding" || name == "MaybeUninit" || name == "Option" {
                    if let Some(args) = seg.args {
                        for arg in args.args {
                            if let rustc_hir::GenericArg::Type(ty) = arg {
                                return format_ambig_ty(tcx, renames, ty);
                            }
                        }
                    }
                }
                // Only apply type renames in type context (turbofish=false).
                // In expression context (turbofish=true), paths refer to values.
                let base = resolve_primitive(name)
                    .unwrap_or_else(|| if turbofish { name.to_string() } else { resolve_name(name, renames) });
                let generic_str = format_segment_generic_args(tcx, renames, seg, turbofish);
                format!("{}{}", base, generic_str)
            } else {
                "/* unknown path */".to_string()
            }
        }
        rustc_hir::QPath::TypeRelative(ty, seg) => {
            let ty_str = format_ty(tcx, renames, ty);
            // Padding::uninit() / MaybeUninit::uninit() → uninitialized
            if (ty_str == "Padding" || ty_str == "MaybeUninit") && seg.ident.as_str() == "uninit" {
                return "uninitialized".to_string();
            }
            let generic_str = format_segment_generic_args(tcx, renames, seg, turbofish);
            format!("{}::{}{}", ty_str, seg.ident, generic_str)
        }
    }
}

/// Map Rust primitive names to .alu names (most are the same).
/// Check if a HIR type contains any inferred (`_`) parts.
fn ty_contains_infer(ty: &rustc_hir::Ty) -> bool {
    use rustc_hir::TyKind;
    match &ty.kind {
        TyKind::Infer(()) => true,
        TyKind::Ptr(mt) | TyKind::Ref(_, mt) => ty_contains_infer(mt.ty),
        TyKind::Slice(inner) => ty_contains_infer(inner),
        TyKind::Array(inner, _) => ty_contains_infer(inner),
        _ => false,
    }
}

fn resolve_primitive(name: &str) -> Option<String> {
    match name {
        "i8" | "i16" | "i32" | "i64" | "i128" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "f32" | "f64" | "bool" | "usize" | "isize" => Some(name.to_string()),
        _ => None,
    }
}

/// Format a function return type.
fn format_fn_ret(tcx: TyCtxt<'_>, renames: &Renames, output: &rustc_hir::FnRetTy) -> String {
    match output {
        rustc_hir::FnRetTy::DefaultReturn(_) => String::new(),
        rustc_hir::FnRetTy::Return(ty) => format!(" -> {}", format_ty(tcx, renames, ty)),
    }
}

/// Format a const arg (used in array lengths).
fn format_const_arg(tcx: TyCtxt<'_>, renames: &Renames, c: &rustc_hir::ConstArg) -> String {
    use rustc_hir::ConstArgKind;
    match &c.kind {
        ConstArgKind::Anon(anon) => {
            let def_id = anon.def_id.to_def_id();
            if let Ok(ConstValue::Scalar(scalar)) = tcx.const_eval_poly(def_id) {
                if let Ok(si) = scalar.try_to_scalar_int() {
                    return format!("{}", si.to_u64());
                }
            }
            format_anon_const_expr(tcx, renames, anon)
        }
        ConstArgKind::Path(qpath) => format_qpath(tcx, renames, qpath, false),
        _ => "/* const */".to_string(),
    }
}

/// Try to format an anonymous const expression from its HIR body.
fn format_anon_const_expr(tcx: TyCtxt<'_>, renames: &Renames, anon: &rustc_hir::AnonConst) -> String {
    let body = tcx.hir_body(anon.body);
    format_expr(tcx, renames, &body.value)
}

/// Format a HIR expression as .alu syntax (for const expressions in array lengths etc.).
/// Falls back to `/* expr */` for unsupported expressions.
fn format_expr(tcx: TyCtxt<'_>, renames: &Renames, expr: &rustc_hir::Expr) -> String {
    let empty = HashSet::new();
    try_format_expr(tcx, renames, &empty, expr).unwrap_or_else(|_| "/* expr */".to_string())
}

/// Try to format a HIR expression as .alu syntax. Returns Err for unsupported expressions.
fn try_format_expr(
    tcx: TyCtxt<'_>,
    renames: &Renames,
    all_type_names: &HashSet<String>,
    expr: &rustc_hir::Expr,
) -> Result<String, ()> {
    use rustc_hir::ExprKind;
    match &expr.kind {
        ExprKind::Lit(lit) => {
            use rustc_ast::LitKind;
            match &lit.node {
                LitKind::Int(n, _) => Ok(format!("{}", n)),
                LitKind::Float(sym, _) => Ok(sym.to_string()),
                LitKind::Bool(b) => Ok(format!("{}", b)),
                _ => Err(()),
            }
        }
        ExprKind::Unary(op, inner) => {
            let inner_str = try_format_expr(tcx, renames, all_type_names, inner)?;
            match op {
                rustc_hir::UnOp::Neg => Ok(format!("-({})", inner_str)),
                rustc_hir::UnOp::Not => Ok(format!("!({})", inner_str)),
                rustc_hir::UnOp::Deref => Ok(format!("*({})", inner_str)),
            }
        }
        ExprKind::Binary(op, lhs, rhs) => {
            let lhs_str = try_format_expr(tcx, renames, all_type_names, lhs)?;
            let rhs_str = try_format_expr(tcx, renames, all_type_names, rhs)?;
            let op_str = match op.node {
                rustc_hir::BinOpKind::Add => "+",
                rustc_hir::BinOpKind::Sub => "-",
                rustc_hir::BinOpKind::Mul => "*",
                rustc_hir::BinOpKind::Div => "/",
                rustc_hir::BinOpKind::Rem => "%",
                rustc_hir::BinOpKind::BitAnd => "&",
                rustc_hir::BinOpKind::BitOr => "|",
                rustc_hir::BinOpKind::BitXor => "^",
                rustc_hir::BinOpKind::Shl => "<<",
                rustc_hir::BinOpKind::Shr => ">>",
                rustc_hir::BinOpKind::Eq => "==",
                rustc_hir::BinOpKind::Ne => "!=",
                rustc_hir::BinOpKind::Lt => "<",
                rustc_hir::BinOpKind::Le => "<=",
                rustc_hir::BinOpKind::Gt => ">",
                rustc_hir::BinOpKind::Ge => ">=",
                rustc_hir::BinOpKind::And => "&&",
                rustc_hir::BinOpKind::Or => "||",
            };
            Ok(format!("({} {} {})", lhs_str, op_str, rhs_str))
        }
        ExprKind::Cast(inner, ty) => {
            let inner_str = try_format_expr(tcx, renames, all_type_names, inner)?;
            if ty_contains_infer(ty) {
                Ok(format!("std::util::cast({})", inner_str))
            } else {
                Ok(format!("({} as {})", inner_str, format_ty(tcx, renames, ty)))
            }
        }
        ExprKind::Path(qpath) => Ok(format_qpath(tcx, renames, qpath, true)),
        ExprKind::Block(block, _) => {
            if block.stmts.is_empty() {
                if let Some(expr) = &block.expr {
                    return try_format_expr(tcx, renames, all_type_names, expr);
                }
                return Ok("()".to_string());
            }
            // Multi-statement block as inline expression
            let mut parts = Vec::new();
            for stmt in block.stmts {
                parts.push(try_format_stmt(tcx, renames, all_type_names, stmt)?);
            }
            if let Some(tail) = &block.expr {
                parts.push(try_format_expr(tcx, renames, all_type_names, tail)?);
            }
            Ok(format!("{{ {} }}", parts.join(" ")))
        }
        ExprKind::If(cond, then_expr, else_opt) => {
            let cond_str = try_format_expr(tcx, renames, all_type_names, cond)?;
            let then_str = try_format_expr(tcx, renames, all_type_names, then_expr)?;
            if let Some(else_expr) = else_opt {
                let else_str = try_format_expr(tcx, renames, all_type_names, else_expr)?;
                Ok(format!("if {} {{ {} }} else {{ {} }}", cond_str, then_str, else_str))
            } else {
                Ok(format!("if {} {{ {} }}", cond_str, then_str))
            }
        }
        ExprKind::Call(func, args) => {
            let func_str = try_format_expr(tcx, renames, all_type_names, func)?;
            let args_str: Result<Vec<_>, _> = args
                .iter()
                .map(|a| try_format_expr(tcx, renames, all_type_names, a))
                .collect();
            Ok(format!("{}({})", func_str, args_str?.join(", ")))
        }
        ExprKind::Struct(qpath, fields, base) => {
            if !matches!(base, rustc_hir::StructTailExpr::None) {
                return Err(()); // `..base` not supported
            }
            let name = format_qpath(tcx, renames, qpath, false);
            let fields_str: Result<Vec<_>, _> = fields
                .iter()
                .map(|f| {
                    let val = try_format_expr(tcx, renames, all_type_names, f.expr)?;
                    let field_name = f.ident.as_str();
                    let field_name = if all_type_names.contains(field_name) {
                        format!("{}_", field_name)
                    } else {
                        field_name.to_string()
                    };
                    Ok(format!("{}: {}", field_name, val))
                })
                .collect();
            Ok(format!("{} {{ {} }}", name, fields_str?.join(", ")))
        }
        ExprKind::Array(exprs) => {
            let elems: Result<Vec<_>, _> = exprs
                .iter()
                .map(|e| try_format_expr(tcx, renames, all_type_names, e))
                .collect();
            Ok(format!("[{}]", elems?.join(", ")))
        }
        ExprKind::Repeat(inner, count) => {
            let inner_str = try_format_expr(tcx, renames, all_type_names, inner)?;
            // Alumina doesn't support [expr; N] syntax, spell it out
            if let rustc_hir::ConstArgKind::Anon(anon) = &count.kind {
                let def_id = anon.def_id.to_def_id();
                if let Ok(ConstValue::Scalar(scalar)) = tcx.const_eval_poly(def_id) {
                    if let Ok(si) = scalar.try_to_scalar_int() {
                        let n = si.to_u64() as usize;
                        let elems = vec![inner_str; n];
                        return Ok(format!("[{}]", elems.join(", ")));
                    }
                }
            }
            Err(()) // Can't determine repeat count
        }
        ExprKind::Ret(Some(inner)) => {
            let inner_str = try_format_expr(tcx, renames, all_type_names, inner)?;
            Ok(format!("return {}", inner_str))
        }
        ExprKind::Ret(None) => Ok("return".to_string()),
        ExprKind::DropTemps(inner) => try_format_expr(tcx, renames, all_type_names, inner),
        ExprKind::Field(inner, ident) => {
            let inner_str = try_format_expr(tcx, renames, all_type_names, inner)?;
            Ok(format!("{}.{}", inner_str, ident))
        }
        ExprKind::Index(arr, idx, _) => {
            let arr_str = try_format_expr(tcx, renames, all_type_names, arr)?;
            let idx_str = try_format_expr(tcx, renames, all_type_names, idx)?;
            Ok(format!("{}[{}]", arr_str, idx_str))
        }
        ExprKind::Assign(lhs, rhs, _) => {
            let lhs_str = try_format_expr(tcx, renames, all_type_names, lhs)?;
            let rhs_str = try_format_expr(tcx, renames, all_type_names, rhs)?;
            Ok(format!("{} = {}", lhs_str, rhs_str))
        }
        ExprKind::AssignOp(op, lhs, rhs) => {
            let lhs_str = try_format_expr(tcx, renames, all_type_names, lhs)?;
            let rhs_str = try_format_expr(tcx, renames, all_type_names, rhs)?;
            Ok(format!("{} {} {}", lhs_str, op.node.as_str(), rhs_str))
        }
        ExprKind::AddrOf(_, _mutbl, inner) => {
            let inner_str = try_format_expr(tcx, renames, all_type_names, inner)?;
            Ok(format!("&{}", inner_str))
        }
        ExprKind::Tup(exprs) => {
            let parts: Result<Vec<_>, _> = exprs
                .iter()
                .map(|e| try_format_expr(tcx, renames, all_type_names, e))
                .collect();
            Ok(format!("({})", parts?.join(", ")))
        }
        _ => Err(()),
    }
}

/// Try to format a pattern.
fn try_format_pat(pat: &rustc_hir::Pat) -> Result<String, ()> {
    match &pat.kind {
        rustc_hir::PatKind::Binding(_, _, ident, _) => Ok(ident.as_str().to_string()),
        rustc_hir::PatKind::Wild => Ok("_".to_string()),
        _ => Err(()),
    }
}

/// Try to format a statement.
fn try_format_stmt(
    tcx: TyCtxt<'_>,
    renames: &Renames,
    all_type_names: &HashSet<String>,
    stmt: &rustc_hir::Stmt,
) -> Result<String, ()> {
    use rustc_hir::StmtKind;
    match &stmt.kind {
        StmtKind::Let(local) => {
            let pat = try_format_pat(local.pat)?;
            let init = local
                .init
                .as_ref()
                .map(|e| try_format_expr(tcx, renames, all_type_names, e))
                .transpose()?;
            let ty_ann = local
                .ty
                .map(|t| format!(": {}", format_ty(tcx, renames, t)))
                .unwrap_or_default();
            if let Some(init) = init {
                Ok(format!("let {}{} = {};", pat, ty_ann, init))
            } else {
                Ok(format!("let {}{};", pat, ty_ann))
            }
        }
        StmtKind::Expr(expr) => try_format_expr(tcx, renames, all_type_names, expr),
        StmtKind::Semi(expr) => {
            let s = try_format_expr(tcx, renames, all_type_names, expr)?;
            Ok(format!("{};", s))
        }
        _ => Err(()),
    }
}

/// Try to format a function body. Returns the indented body lines.
fn try_format_fn_body(
    tcx: TyCtxt<'_>,
    renames: &Renames,
    all_type_names: &HashSet<String>,
    expr: &rustc_hir::Expr,
) -> Result<String, ()> {
    use rustc_hir::ExprKind;
    match &expr.kind {
        ExprKind::Block(block, _) => {
            let mut lines = Vec::new();
            for stmt in block.stmts {
                lines.push(format!(
                    "    {}",
                    try_format_stmt(tcx, renames, all_type_names, stmt)?
                ));
            }
            if let Some(tail) = &block.expr {
                lines.push(format!(
                    "    {}",
                    try_format_expr(tcx, renames, all_type_names, tail)?
                ));
            }
            Ok(lines.join("\n"))
        }
        _ => Ok(format!(
            "    {}",
            try_format_expr(tcx, renames, all_type_names, expr)?
        )),
    }
}

/// Try to evaluate a constant and format it as a string.
fn eval_const(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    let result = tcx.const_eval_poly(def_id).ok()?;
    match result {
        ConstValue::Scalar(scalar) => {
            let ty = tcx.type_of(def_id).skip_binder();
            format_scalar(scalar, ty)
        }
        _ => None,
    }
}

/// Format a scalar value based on its type.
fn format_scalar(
    scalar: rustc_middle::mir::interpret::Scalar,
    ty: rustc_middle::ty::Ty<'_>,
) -> Option<String> {
    use rustc_middle::ty::TyKind;
    let scalar_int = scalar.try_to_scalar_int().ok()?;
    match ty.kind() {
        TyKind::Int(int_ty) => {
            let val: i128 = match int_ty {
                rustc_middle::ty::IntTy::I8 => scalar_int.to_i8() as i128,
                rustc_middle::ty::IntTy::I16 => scalar_int.to_i16() as i128,
                rustc_middle::ty::IntTy::I32 => scalar_int.to_i32() as i128,
                rustc_middle::ty::IntTy::I64 => scalar_int.to_i64() as i128,
                rustc_middle::ty::IntTy::I128 => scalar_int.to_i128(),
                rustc_middle::ty::IntTy::Isize => scalar_int.to_i64() as i128,
            };
            Some(format!("{}", val))
        }
        TyKind::Uint(uint_ty) => {
            let val: u128 = match uint_ty {
                rustc_middle::ty::UintTy::U8 => scalar_int.to_u8() as u128,
                rustc_middle::ty::UintTy::U16 => scalar_int.to_u16() as u128,
                rustc_middle::ty::UintTy::U32 => scalar_int.to_u32() as u128,
                rustc_middle::ty::UintTy::U64 => scalar_int.to_u64() as u128,
                rustc_middle::ty::UintTy::U128 => scalar_int.to_u128(),
                rustc_middle::ty::UintTy::Usize => scalar_int.to_u64() as u128,
            };
            Some(format!("{}", val))
        }
        TyKind::Float(float_ty) => match float_ty {
            rustc_middle::ty::FloatTy::F32 => {
                Some(format!("{}", f32::from_bits(scalar_int.to_u32())))
            }
            rustc_middle::ty::FloatTy::F64 => {
                Some(format!("{}", f64::from_bits(scalar_int.to_u64())))
            }
            _ => None,
        },
        TyKind::Bool => {
            let val = scalar_int.try_to_bool().ok()?;
            Some(format!("{}", val))
        }
        _ => None,
    }
}

/// Emit the .alu cfg header line.
fn emit_cfg_header(out: &mut impl Write, target: &str) -> io::Result<()> {
    let parts: Vec<&str> = target.split('-').collect();
    let (arch, os, env) = match parts.as_slice() {
        [arch, _vendor, os, env] => (*arch, *os, Some(*env)),
        [arch, _vendor, os] => (*arch, *os, None),
        [arch, os] => (*arch, *os, None),
        _ => ("unknown", "unknown", None),
    };

    let target_os = match os {
        "linux" => "linux",
        "darwin" | "macos" => "macos",
        "android" => "android",
        other => other,
    };

    if let Some(env) = env {
        writeln!(
            out,
            "#![cfg(all(target_env = \"{}\", target_arch = \"{}\", target_os = \"{}\"))]",
            env, arch, target_os
        )?;
    } else {
        writeln!(
            out,
            "#![cfg(all(target_arch = \"{}\", target_os = \"{}\"))]",
            arch, target_os
        )?;
    }
    Ok(())
}

impl rustc_driver::Callbacks for AluDumper {
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        let mut out = io::BufWriter::new(&mut self.output);

        let target = tcx.sess.opts.target_triple.tuple().to_string();
        emit_cfg_header(&mut out, &target).unwrap();
        writeln!(out).unwrap();
        writeln!(out, "#![allow(unused_parameter)]").unwrap();
        writeln!(out, "use libc::helpers::*;").unwrap();
        writeln!(out).unwrap();

        // Pass 1: collect all names to detect conflicts
        let mut value_names = HashSet::new();
        let mut type_names = HashSet::new();
        let mut seen = HashSet::new();
        for id in tcx.hir_free_items() {
            let item = tcx.hir_item(id);
            collect_names(tcx, &mut seen, item, &mut value_names, &mut type_names);
        }
        let renames = build_renames(&value_names, &type_names);
        if !renames.is_empty() {
            eprintln!(
                "Note: renamed {} types to avoid name conflicts: {:?}",
                renames.len(),
                renames
            );
        }
        let all_type_names = build_all_type_names(&type_names, &renames);

        // Pass 2: emit items
        let mut seen = HashSet::new();
        for id in tcx.hir_free_items() {
            let item = tcx.hir_item(id);
            emit_item(&mut out, tcx, &renames, &all_type_names, &mut seen, item);
        }

        out.flush().unwrap();
        Compilation::Stop
    }
}

fn emit_item(
    out: &mut impl Write,
    tcx: TyCtxt<'_>,
    renames: &Renames,
    all_type_names: &HashSet<String>,
    seen: &mut HashSet<DefId>,
    item: &rustc_hir::Item,
) {
    use rustc_hir::ItemKind;

    if let ItemKind::Mod(_ident, module) = &item.kind {
        for &item_id in module.item_ids {
            let child = tcx.hir_item(item_id);
            emit_item(out, tcx, renames, all_type_names, seen, child);
        }
        return;
    }

    if let ItemKind::ForeignMod { abi: _, items } = &item.kind {
        for &foreign_item_id in *items {
            let foreign_item = tcx.hir_foreign_item(foreign_item_id);
            let def_id = foreign_item.owner_id.def_id.to_def_id();
            if seen.insert(def_id) {
                emit_foreign_item(out, tcx, renames, all_type_names, foreign_item);
            }
        }
        return;
    }

    let def_id = item.owner_id.def_id.to_def_id();
    if !seen.insert(def_id) {
        return;
    }

    match &item.kind {
        ItemKind::TyAlias(ident, _generics, ty) => {
            let name = resolve_name(ident.as_str(), renames);
            let ty_str = format_ty(tcx, renames, ty);
            writeln!(out, "type {} = {};", name, ty_str).unwrap();
        }
        ItemKind::Struct(ident, _generics, variant_data) => {
            if ident.as_str() == "Padding" {
                return;
            }
            let name = resolve_name(ident.as_str(), renames);
            emit_align_attr(out, tcx, def_id);
            emit_struct_or_union(out, tcx, renames, all_type_names, "struct", &name, variant_data);
        }
        ItemKind::Union(ident, _generics, variant_data) => {
            let name = resolve_name(ident.as_str(), renames);
            emit_align_attr(out, tcx, def_id);
            emit_struct_or_union(out, tcx, renames, all_type_names, "union", &name, variant_data);
        }
        ItemKind::Enum(ident, _generics, enum_def) => {
            if enum_def.variants.is_empty() {
                let name = resolve_name(ident.as_str(), renames);
                writeln!(out, "enum {} {{}}", name).unwrap();
            }
        }
        ItemKind::Const(ident, _generics, ty, rhs) => {
            let ty_str = format_ty(tcx, renames, ty);
            if let Some(val) = eval_const(tcx, def_id) {
                writeln!(out, "const {}: {} = {};", ident, ty_str, val).unwrap();
            } else if let rustc_hir::ConstItemRhs::Body(body_id) = rhs {
                // Try to format the HIR body (for struct/array initializers)
                let body = tcx.hir_body(*body_id);
                if let Ok(expr_str) =
                    try_format_expr(tcx, renames, all_type_names, &body.value)
                {
                    writeln!(out, "const {}: {} = {};", ident, ty_str, expr_str).unwrap();
                } else {
                    writeln!(
                        out,
                        "// const {}: {} = /* could not evaluate */;",
                        ident, ty_str
                    )
                    .unwrap();
                }
            } else {
                writeln!(
                    out,
                    "// const {}: {} = /* could not evaluate */;",
                    ident, ty_str
                )
                .unwrap();
            }
        }
        ItemKind::Fn { ident, sig, generics, body, .. } => {
            let name = ident.as_str();
            let body = tcx.hir_body(*body);
            let decl = sig.decl;
            writeln!(out, "#[inline(always)]").unwrap();
            // Format generic type parameters
            let generic_params: Vec<String> = generics
                .params
                .iter()
                .filter_map(|p| {
                    if let rustc_hir::GenericParamKind::Type { .. } = p.kind {
                        Some(p.name.ident().as_str().to_string())
                    } else {
                        None
                    }
                })
                .collect();
            let generics_str = if generic_params.is_empty() {
                String::new()
            } else {
                format!("<{}>", generic_params.join(", "))
            };
            let params: Vec<String> = decl
                .inputs
                .iter()
                .zip(body.params.iter())
                .map(|(ty, param)| {
                    let ty_str = format_ty(tcx, renames, ty);
                    let param_name = try_format_pat(param.pat)
                        .unwrap_or_else(|_| "_".to_string());
                    let param_name = if all_type_names.contains(param_name.as_str()) {
                        format!("{}_", param_name)
                    } else {
                        param_name
                    };
                    format!("{}: {}", param_name, ty_str)
                })
                .collect();
            let ret = format_fn_ret(tcx, renames, &decl.output);
            match try_format_fn_body(tcx, renames, all_type_names, &body.value) {
                Ok(body_str) => {
                    writeln!(out, "fn {}{}({}){} {{", name, generics_str, params.join(", "), ret).unwrap();
                    writeln!(out, "{}", body_str).unwrap();
                    writeln!(out, "}}").unwrap();
                }
                Err(()) => {
                    writeln!(out, "fn {}{}({}){} {{", name, generics_str, params.join(", "), ret).unwrap();
                    writeln!(out, "    compile_fail!(\"unsupported\")").unwrap();
                    writeln!(out, "}}").unwrap();
                }
            }
        }
        _ => {}
    }
}

fn emit_align_attr(out: &mut impl Write, tcx: TyCtxt<'_>, def_id: DefId) {
    let adt_def = tcx.adt_def(def_id);
    let repr = adt_def.repr();
    if let Some(align) = repr.align {
        writeln!(out, "#[align({})]", align.bytes()).unwrap();
    }
}

fn emit_struct_or_union(
    out: &mut impl Write,
    tcx: TyCtxt<'_>,
    renames: &Renames,
    all_type_names: &HashSet<String>,
    keyword: &str,
    name: &str,
    variant_data: &rustc_hir::VariantData,
) {
    let fields: Vec<_> = variant_data.fields().iter().collect();
    if fields.is_empty() {
        writeln!(out, "{} {} {{}}", keyword, name).unwrap();
        return;
    }

    writeln!(out, "{} {} {{", keyword, name).unwrap();
    for field in &fields {
        let field_name = field.ident.as_str();
        let field_name = if all_type_names.contains(field_name) {
            format!("{}_", field_name)
        } else {
            field_name.to_string()
        };
        let ty_str = format_ty(tcx, renames, field.ty);
        writeln!(out, "    {}: {},", field_name, ty_str).unwrap();
    }
    writeln!(out, "}}").unwrap();
}

fn emit_foreign_item(
    out: &mut impl Write,
    tcx: TyCtxt<'_>,
    renames: &Renames,
    all_type_names: &HashSet<String>,
    item: &rustc_hir::ForeignItem,
) {
    match &item.kind {
        rustc_hir::ForeignItemKind::Fn(sig, param_idents, _generics) => {
            let decl = sig.decl;
            let params: Vec<String> = decl
                .inputs
                .iter()
                .zip(param_idents.iter())
                .map(|(ty, ident)| {
                    let ty_str = format_ty(tcx, renames, ty);
                    if let Some(ident) = ident {
                        let name = ident.as_str();
                        let param_name = if all_type_names.contains(name) {
                            format!("{}_", name)
                        } else {
                            name.to_string()
                        };
                        format!("{}: {}", param_name, ty_str)
                    } else {
                        format!("_: {}", ty_str)
                    }
                })
                .collect();
            let ret = format_fn_ret(tcx, renames, &decl.output);
            let params_str = if decl.c_variadic {
                format!("{}, ...", params.join(", "))
            } else {
                params.join(", ")
            };
            writeln!(
                out,
                "extern \"C\" fn {}({}){};",
                item.ident,
                params_str,
                ret
            )
            .unwrap();
        }
        rustc_hir::ForeignItemKind::Static(ty, mutbl, _safety) => {
            let ty_str = format_ty(tcx, renames, ty);
            match mutbl {
                rustc_hir::Mutability::Mut => {
                    writeln!(out, "extern \"C\" static mut {}: {};", item.ident, ty_str).unwrap();
                }
                rustc_hir::Mutability::Not => {
                    writeln!(out, "extern \"C\" static {}: {};", item.ident, ty_str).unwrap();
                }
            }
        }
        rustc_hir::ForeignItemKind::Type => {
            let name = resolve_name(item.ident.as_str(), renames);
            writeln!(out, "enum {} {{}}", name).unwrap();
        }
    }
}

/// Generate Alumina libc bindings (.alu) from the Rust libc crate.
#[derive(Parser)]
struct Args {
    /// Path to the libc crate's lib.rs
    lib_path: String,

    /// Output directory for generated .alu files
    #[arg(short, long)]
    output: PathBuf,

    /// Target triples to generate bindings for
    #[arg(short, long, required = true)]
    target: Vec<String>,
}

fn target_to_filename(target: &str) -> String {
    format!("{}.alu", target.replace('-', "_"))
}

fn main() {
    let args = Args::parse();

    fs::create_dir_all(&args.output).unwrap_or_else(|e| {
        eprintln!("Cannot create output directory {}: {}", args.output.display(), e);
        std::process::exit(1);
    });

    for target in &args.target {
        let output_path = args.output.join(target_to_filename(target));
        eprintln!("Generating {} ...", output_path.display());

        let file = fs::File::create(&output_path).unwrap_or_else(|e| {
            panic!("Cannot create {}: {}", output_path.display(), e);
        });

        let compiler_args: Vec<String> = vec![
            "libc-dumper".to_string(),
            args.lib_path.clone(),
            "--edition=2021".to_string(),
            "--target".to_string(),
            target.clone(),
        ];

        let mut dumper = AluDumper {
            output: Box::new(file),
        };

        run_compiler(&compiler_args, &mut dumper);
    }
}
