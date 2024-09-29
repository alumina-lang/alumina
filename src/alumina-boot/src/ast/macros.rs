use crate::ast::expressions::ExpressionVisitor;
use crate::ast::format::{format_args, Piece};
use crate::ast::pretty::PrettyPrinter;
use crate::ast::{
    AstCtx, Attribute, BuiltinMacro, BuiltinMacroKind, Expr, ExprKind, ExprP, FieldInitializer,
    FnKind, Id, Item, ItemP, Lit, Macro, MacroCtx, MacroParameter, Span, Statement,
};
use crate::common::{AluminaError, ArenaAllocatable, CodeDiagnostic, HashMap};
use crate::global_ctx::GlobalCtx;
use crate::parser::{FieldKind, NodeExt};
use crate::src::scope::{NamedItemKind, Scope};

use once_cell::unsync::OnceCell;

use super::TyP;

pub struct MacroMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,
}

macro_rules! assert_args {
    ($self:expr, $count:expr) => {
        if $self.args.len() != $count {
            use crate::common::CodeErrorBuilder;
            return Err(CodeDiagnostic::ParamCountMismatch($count, $self.args.len()))
                .with_span($self.invocation_span);
        }
    };
}

macro_rules! string_arg {
    ($self:expr, $index:expr) => {
        match $self.args[$index].kind {
            ExprKind::Lit(Lit::Str(s)) => s,
            _ => {
                use crate::common::CodeErrorBuilder;
                return Err(CodeDiagnostic::ConstantStringExpected)
                    .with_span($self.invocation_span);
            }
        }
    };
}

macro_rules! macro_arg {
    ($self:expr, $index:expr) => {
        match $self.args[$index].kind {
            ExprKind::Macro(item, bound_args) => (item, bound_args),
            _ => {
                use crate::common::CodeErrorBuilder;
                return Err(CodeDiagnostic::NotAMacro).with_span($self.invocation_span);
            }
        }
    };
}

impl<'ast> MacroMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, global_ctx: GlobalCtx) -> Self {
        Self { ast, global_ctx }
    }

    pub fn make<'src>(
        &mut self,
        name: Option<&'ast str>,
        item: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        use crate::common::WithSpanDuringParsing;

        if let Some(inner) = item.try_get() {
            match inner {
                Item::Macro(m) => {
                    if m.body.get().is_some() {
                        return Ok(());
                    } else {
                        return Err(CodeDiagnostic::RecursiveMacroCall)
                            .with_span_from(&scope, node);
                    }
                }
                Item::BuiltinMacro(_) => {
                    return Ok(());
                }
                _ => unreachable!(),
            }
        }

        let mut parameters = Vec::new();
        let mut has_et_cetera = false;

        let span = Span::from_node(scope.file_id(), node);

        if attributes.iter().any(|a| matches!(a, Attribute::Builtin)) {
            let kind = match name.unwrap() {
                "env" => BuiltinMacroKind::Env,
                "cfg" => BuiltinMacroKind::Cfg,
                "include_bytes" => BuiltinMacroKind::IncludeBytes,
                "concat" => BuiltinMacroKind::Concat,
                "line" => BuiltinMacroKind::Line,
                "column" => BuiltinMacroKind::Column,
                "file" => BuiltinMacroKind::File,
                "format_args" => BuiltinMacroKind::FormatArgs,
                "bind" => BuiltinMacroKind::Bind,
                "reduce" => BuiltinMacroKind::Reduce,
                "stringify" => BuiltinMacroKind::Stringify,
                s => {
                    return Err(CodeDiagnostic::UnknownBuiltinMacro(s.to_string()))
                        .with_span_from(&scope, node)
                }
            };

            item.assign(Item::BuiltinMacro(BuiltinMacro {
                kind,
                span: Some(span),
            }));

            return Ok(());
        }

        for (_name, item) in scope.inner().all_items() {
            match item.kind {
                NamedItemKind::MacroParameter(id, et_cetera) => {
                    if has_et_cetera && et_cetera {
                        return Err(CodeDiagnostic::MultipleMacroEtCeteras)
                            .with_span_from(&scope, node);
                    } else if et_cetera {
                        has_et_cetera = true;
                    }

                    let span = Span::from_node(scope.file_id(), node);

                    parameters.push(MacroParameter {
                        id,
                        et_cetera,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let result = Item::Macro(Macro {
            name,
            args: parameters.alloc_on(self.ast),
            body: OnceCell::new(),
            span: Some(span),
        });

        item.assign(result);

        let body = ExpressionVisitor::new(
            self.ast,
            self.global_ctx.clone(),
            scope.clone(),
            MacroCtx::for_macro(has_et_cetera),
        )
        .generate(node.child_by_field(FieldKind::Body).unwrap())?;

        scope.check_unused_items(&self.global_ctx.diag());

        // Two-step assignment to detect recursion
        item.get_macro().body.set(body).unwrap();

        Ok(())
    }
}

pub struct MacroExpander<'ast> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,

    r#macro: ItemP<'ast>,
    args: Vec<ExprP<'ast>>,
    invocation_span: Option<Span>,

    replacements: HashMap<Id, ExprP<'ast>>,
    id_replacements: HashMap<Id, Id>,
    et_cetera_arg: Option<(Id, Vec<ExprP<'ast>>)>,

    et_cetera_index: Option<usize>,
}

impl<'ast> MacroExpander<'ast> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        global_ctx: GlobalCtx,
        invocation_span: Option<Span>,
        r#macro: ItemP<'ast>,
        arguments: Vec<ExprP<'ast>>,
    ) -> Self {
        Self {
            ast,
            global_ctx,
            r#macro,
            args: arguments,
            invocation_span,
            replacements: HashMap::default(),
            id_replacements: HashMap::default(),
            et_cetera_arg: None,
            et_cetera_index: None,
        }
    }

    pub fn expand(self) -> Result<ExprP<'ast>, AluminaError> {
        match self.r#macro.get() {
            Item::Macro(m) => self.expand_regular(m),
            Item::BuiltinMacro(BuiltinMacro { kind, .. }) => self.expand_builtin(kind),
            _ => unreachable!(),
        }
    }

    fn expand_regular(mut self, r#macro: &'ast Macro<'ast>) -> Result<ExprP<'ast>, AluminaError> {
        use crate::common::CodeErrorBuilder;

        let et_cetera_index = r#macro.args.iter().position(|arg| arg.et_cetera);

        if let Some(et_cetera_index) = et_cetera_index {
            if self.args.len() < r#macro.args.len() - 1 {
                return Err(CodeDiagnostic::NotEnoughMacroArguments(
                    r#macro.args.len() - 1,
                ))
                .with_span(self.invocation_span);
            }
            let etc_count = self.args.len() + 1 - r#macro.args.len();

            for i in 0..et_cetera_index {
                self.replacements.insert(r#macro.args[i].id, self.args[i]);
            }

            let etc_args: Vec<_> = self.args[et_cetera_index..et_cetera_index + etc_count].to_vec();

            for i in et_cetera_index + 1..r#macro.args.len() {
                self.replacements
                    .insert(r#macro.args[i].id, self.args[i + etc_count - 1]);
            }

            self.et_cetera_arg = Some((r#macro.args[et_cetera_index].id, etc_args));
        } else {
            if self.args.len() != r#macro.args.len() {
                return Err(CodeDiagnostic::ParamCountMismatch(
                    r#macro.args.len(),
                    self.args.len(),
                ))
                .with_span(self.invocation_span);
            }

            for (i, arg) in r#macro.args.iter().enumerate() {
                self.replacements.insert(arg.id, self.args[i]);
            }
        }

        self.visit_expr(r#macro.body.get().unwrap())
    }

    fn expand_args(&mut self, args: &[ExprP<'ast>]) -> Result<&'ast [ExprP<'ast>], AluminaError> {
        use crate::common::CodeErrorBuilder;

        let mut new_args = Vec::new();
        for arg in args {
            if let super::ExprKind::EtCeteraMacro(inner) = arg.kind {
                if self.et_cetera_index.is_some() {
                    return Err(CodeDiagnostic::MacroEtCeteraInMacroEtCetera).with_span(arg.span);
                }
                for idx in 0..self.et_cetera_arg.as_ref().unwrap().1.len() {
                    self.et_cetera_index = Some(idx);
                    new_args.push(self.visit_expr(inner)?);
                }
                self.et_cetera_index = None;
            } else {
                new_args.push(self.visit_expr(arg)?);
            }
        }

        Ok(new_args.alloc_on(self.ast))
    }

    fn visit_ty(&mut self, ty: TyP<'ast>) -> Result<TyP<'ast>, AluminaError> {
        use crate::ast::Ty::*;

        let ret = match ty {
            Tag(tag, inner) => Tag(tag, self.visit_ty(inner)?),
            Pointer(inner, a) => Pointer(self.visit_ty(inner)?, *a),
            Slice(inner, a) => Slice(self.visit_ty(inner)?, *a),
            Dyn(protos, a) => {
                let elements = protos
                    .iter()
                    .map(|ty| self.visit_ty(ty))
                    .collect::<Result<Vec<_>, _>>()?;

                let slice = elements.alloc_on(self.ast);
                Dyn(slice, *a)
            }
            TypeOf(expr) => TypeOf(self.visit_expr(expr)?),
            Array(inner, len) => Array(self.visit_ty(inner)?, self.visit_expr(len)?),
            Tuple(elems) => {
                let elements = elems
                    .iter()
                    .map(|ty| self.visit_ty(ty))
                    .collect::<Result<Vec<_>, _>>()?;

                let slice = elements.alloc_on(self.ast);
                Tuple(slice)
            }
            When(cond, a, b) => When(self.visit_expr(cond)?, self.visit_ty(a)?, self.visit_ty(b)?),
            FunctionPointer(args, ret) => {
                let elements = args
                    .iter()
                    .map(|ty| self.visit_ty(ty))
                    .collect::<Result<Vec<_>, _>>()?;

                let slice = elements.alloc_on(self.ast);
                FunctionPointer(slice, ret)
            }
            FunctionProtocol(args, ret) => {
                let elements = args
                    .iter()
                    .map(|ty| self.visit_ty(ty))
                    .collect::<Result<Vec<_>, _>>()?;

                let slice = elements.alloc_on(self.ast);
                FunctionProtocol(slice, ret)
            }
            Generic(item, args) => Generic(
                item,
                args.iter()
                    .map(|e| self.visit_ty(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.ast),
            ),
            Defered(super::Defered { ty, name }) => Defered(super::Defered {
                ty: self.visit_ty(ty)?,
                name,
            }),
            EtCetera(inner) => EtCetera(self.visit_ty(inner)?),
            TupleIndex(inner, idx) => TupleIndex(self.visit_ty(inner)?, self.visit_expr(idx)?),
            Deref(inner) => Deref(self.visit_ty(inner)?),
            Placeholder(_) | Item(_) | Builtin(_) => return Ok(ty),
        };

        Ok(self.ast.intern_type(ret))
    }

    fn visit_expr(&mut self, expr: ExprP<'ast>) -> Result<ExprP<'ast>, AluminaError> {
        use crate::ast::ExprKind::*;
        use crate::common::CodeErrorBuilder;

        let kind = match expr.kind {
            Call(callee, args) => Call(self.visit_expr(callee)?, self.expand_args(args)?),
            Tuple(args) => Tuple(self.expand_args(args)?),
            Array(args) => Array(self.expand_args(args)?),
            MacroInvocation(inner, args) => {
                let inner = self.visit_expr(inner)?;
                let (item, bound_args) = match inner.kind {
                    ExprKind::Macro(m, b) => (m, b),
                    _ => return Err(CodeDiagnostic::NotAMacro).with_span(inner.span),
                };
                let child = MacroExpander::new(
                    self.ast,
                    self.global_ctx.clone(),
                    self.invocation_span,
                    item,
                    bound_args
                        .iter()
                        .copied()
                        .chain(self.expand_args(args)?.iter().copied())
                        .collect(),
                );
                return child.expand();
            }

            Local(id) => {
                if let Some(replacement) = self.replacements.get(&id) {
                    return Ok(replacement);
                } else if self.et_cetera_arg.as_ref().map(|v| v.0) == Some(id) {
                    if let Some(index) = self.et_cetera_index {
                        return Ok(self.et_cetera_arg.as_ref().unwrap().1[index]);
                    } else {
                        return Err(CodeDiagnostic::CannotMacroEtCeteraHere).with_span(expr.span);
                    }
                } else {
                    let id = match self.id_replacements.get(&id) {
                        Some(id) => *id,
                        None => {
                            // Macro "captured" some local variables
                            id
                        }
                    };

                    Local(id)
                }
            }
            EtCeteraMacro(_) => {
                return Err(CodeDiagnostic::CannotMacroEtCeteraHere).with_span(expr.span);
            }
            Block(statements, ret) => {
                let mut new_statements = Vec::new();
                for statement in statements {
                    if let super::StatementKind::Expression(Expr {
                        kind: super::ExprKind::EtCeteraMacro(inner),
                        span,
                    }) = statement.kind
                    {
                        if self.et_cetera_index.is_some() {
                            return Err(CodeDiagnostic::MacroEtCeteraInMacroEtCetera)
                                .with_span(*span);
                        }
                        for idx in 0..self.et_cetera_arg.as_ref().unwrap().1.len() {
                            self.et_cetera_index = Some(idx);
                            new_statements.push(Statement {
                                kind: super::StatementKind::Expression(self.visit_expr(inner)?),
                                span: *span,
                            });
                        }
                        self.et_cetera_index = None;
                    } else {
                        new_statements.push(self.visit_stmt(statement)?);
                    }
                }
                Block(new_statements.alloc_on(self.ast), self.visit_expr(ret)?)
            }
            Binary(op, lhs, rhs) => Binary(op, self.visit_expr(lhs)?, self.visit_expr(rhs)?),
            Ref(inner) => Ref(self.visit_expr(inner)?),
            Deref(inner) => Deref(self.visit_expr(inner)?),

            Unary(op, inner) => Unary(op, self.visit_expr(inner)?),
            Assign(lhs, rhs) => Assign(self.visit_expr(lhs)?, self.visit_expr(rhs)?),
            AssignOp(op, lhs, rhs) => AssignOp(op, self.visit_expr(lhs)?, self.visit_expr(rhs)?),
            Loop(inner) => Loop(self.visit_expr(inner)?),
            Break(inner) => Break(inner.map(|i| self.visit_expr(i)).transpose()?),
            Return(inner) => Return(inner.map(|i| self.visit_expr(i)).transpose()?),
            Yield(inner) => Yield(inner.map(|i| self.visit_expr(i)).transpose()?),
            Defer(inner) => Defer(self.visit_expr(inner)?),
            Field(a, name, assoc_fn, generic_args) => Field(
                self.visit_expr(a)?,
                name,
                assoc_fn,
                generic_args
                    .map(|args| {
                        Ok::<_, AluminaError>(
                            args.iter()
                                .map(|e| self.visit_ty(e))
                                .collect::<Result<Vec<_>, _>>()?
                                .alloc_on(self.ast),
                        )
                    })
                    .transpose()?,
            ),
            Struct(ty, inits) => {
                let inits: Vec<_> = inits
                    .iter()
                    .map(|init| {
                        self.visit_expr(init.value).map(|value| FieldInitializer {
                            name: init.name,
                            value,
                            span: self.invocation_span,
                        })
                    })
                    .collect::<Result<_, _>>()?;

                Struct(self.visit_ty(ty)?, inits.alloc_on(self.ast))
            }
            TupleIndex(inner, idx) => TupleIndex(self.visit_expr(inner)?, idx),
            Index(inner, idx) => Index(self.visit_expr(inner)?, self.visit_expr(idx)?),
            Range(lower, upper, inclusive) => Range(
                lower.map(|i| self.visit_expr(i)).transpose()?,
                upper.map(|i| self.visit_expr(i)).transpose()?,
                inclusive,
            ),
            If(condition, then, els) => If(
                self.visit_expr(condition)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
            ),
            StaticIf(cond, then, els) => StaticIf(
                self.visit_expr(cond)?,
                self.visit_expr(then)?,
                self.visit_expr(els)?,
            ),
            StaticFor(id, range, body) => {
                StaticFor(id, self.visit_expr(range)?, self.visit_expr(body)?)
            }
            TypeCheck(expr, ty) => TypeCheck(self.visit_expr(expr)?, self.visit_ty(ty)?),
            Cast(inner, ty) => Cast(self.visit_expr(inner)?, self.visit_ty(ty)?),
            Fn(ref kind, generic_args) => {
                let kind = match kind {
                    FnKind::Normal(_) => *kind,
                    FnKind::Closure(..) => *kind,
                    FnKind::Defered(def) => FnKind::Defered(crate::ast::Defered {
                        ty: self.visit_ty(def.ty)?,
                        name: def.name,
                    }),
                };

                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_ty(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Fn(kind, generic_args)
            }
            Defered(ref def) => Defered(crate::ast::Defered {
                ty: self.visit_ty(def.ty)?,
                name: def.name,
            }),
            Static(item, generic_args) => {
                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_ty(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Static(item, generic_args)
            }
            Const(item, generic_args) => {
                let generic_args = match generic_args {
                    Some(args) => Some(
                        args.iter()
                            .map(|e| self.visit_ty(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .alloc_on(self.ast),
                    ),
                    None => None,
                };

                Const(item, generic_args)
            }
            Tag(tag, inner) => Tag(tag, self.visit_expr(inner)?),
            EtCetera(inner) => EtCetera(self.visit_expr(inner)?),
            Continue
            | EnumValue(_, _)
            | Macro(_, _ /* bound values are "invisible" and should not be replaced */)
            | Lit(_)
            | BoundParam(_, _, _)
            | Void => expr.kind,
        };

        let result = Expr {
            kind,
            span: self.invocation_span,
        };

        Ok(result.alloc_on(self.ast))
    }

    fn visit_stmt(&mut self, stmt: &Statement<'ast>) -> Result<Statement<'ast>, AluminaError> {
        use crate::ast::StatementKind::*;

        let kind = match &stmt.kind {
            Expression(expr) => Expression(self.visit_expr(expr)?),
            LetDeclaration(decl) => {
                // Local variables declared in a macro must be renamed to avoid clashes if
                // same macro is evaluated multiple times in one scope.
                let replacement = self.ast.make_id();
                self.id_replacements.insert(decl.id, replacement);

                LetDeclaration(crate::ast::LetDeclaration {
                    id: replacement,
                    ty: decl.ty.map(|ty| self.visit_ty(ty)).transpose()?,
                    value: decl.value.map(|v| self.visit_expr(v)).transpose()?,
                })
            }
        };

        let result = Statement {
            kind,
            span: self.invocation_span,
        };

        Ok(result)
    }

    fn expand_builtin(&self, kind: &BuiltinMacroKind) -> Result<ExprP<'ast>, AluminaError> {
        use crate::common::CodeErrorBuilder;
        match kind {
            BuiltinMacroKind::Stringify => {
                assert_args!(self, 1);

                let mut printer = PrettyPrinter::new(self.ast);
                let value = self
                    .ast
                    .arena
                    .alloc_slice_copy(printer.print_expr(self.args[0]).as_bytes());

                Ok(Expr {
                    kind: ExprKind::Lit(Lit::Str(value)),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::Env => {
                assert_args!(self, 1);
                let name = string_arg!(self, 0);

                let value: &[u8] = match std::str::from_utf8(name).map(std::env::var) {
                    Ok(Ok(v)) => self.ast.arena.alloc_slice_copy(v.as_bytes()),
                    _ => b"",
                };

                Ok(Expr {
                    kind: ExprKind::Lit(Lit::Str(value)),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::Line | BuiltinMacroKind::Column => {
                let (line, column) = self
                    .invocation_span
                    .map(|s| self.global_ctx.diag().map_span(s))
                    .map(|s| (s.line + 1, s.column.map(|c| c + 1)))
                    .ok_or(CodeDiagnostic::NoSpanInformation)
                    .with_span(self.invocation_span)?;

                let kind = if let BuiltinMacroKind::Line = kind {
                    ExprKind::Lit(Lit::Int(false, line as u128, None))
                } else {
                    ExprKind::Lit(Lit::Int(false, column.unwrap_or(0) as u128, None))
                };

                Ok(Expr {
                    kind,
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::File => {
                assert_args!(self, 0);
                let diag = self.global_ctx.diag();

                let filename = self
                    .invocation_span
                    .map(|s| diag.map_span(s))
                    .and_then(|s| {
                        diag.get_file_path(s.file).map(|filename| {
                            self.ast
                                .arena
                                .alloc_slice_copy(filename.to_string_lossy().as_bytes())
                        })
                    })
                    .ok_or(CodeDiagnostic::NoSpanInformation)
                    .with_span(self.invocation_span)?;

                let kind = ExprKind::Lit(Lit::Str(filename));

                Ok(Expr {
                    kind,
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::IncludeBytes => {
                let filename = match std::str::from_utf8(string_arg!(self, 0)) {
                    Ok(v) => v,
                    _ => unreachable!(),
                };

                let data = std::fs::read(filename)
                    .map_err(|_| CodeDiagnostic::CannotReadFile(filename.to_string()))
                    .with_span(self.invocation_span)?;

                Ok(Expr {
                    kind: ExprKind::Lit(Lit::Str(self.ast.arena.alloc_slice_copy(&data[..]))),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::Concat => {
                let parts = self
                    .args
                    .iter()
                    .map(|arg| match arg.kind {
                        ExprKind::Lit(Lit::Str(s)) => Ok(s),
                        _ => Err(CodeDiagnostic::ConstantStringExpected)
                            .with_span(self.invocation_span),
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let value = self
                    .ast
                    .arena
                    .alloc_slice_fill_default(parts.iter().map(|s| s.len()).sum());

                let mut index = 0;
                for part in parts {
                    value[index..index + part.len()].copy_from_slice(part);
                    index += part.len();
                }

                Ok(Expr {
                    kind: ExprKind::Lit(Lit::Str(value)),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::FormatArgs => {
                if self.args.len() < 2 {
                    return Err(CodeDiagnostic::NotEnoughMacroArguments(2))
                        .with_span(self.invocation_span);
                }

                let (wrapper, bound_args) = macro_arg!(self, 0);
                let fmt_string = string_arg!(self, 1);
                let mut args = bound_args.to_vec();

                for piece in format_args(self.invocation_span, fmt_string, self.args.len() - 2)? {
                    match piece {
                        Piece::String(string_part) => {
                            args.push(
                                Expr {
                                    kind: ExprKind::Lit(Lit::Str(
                                        self.ast.arena.alloc_slice_copy(string_part.as_slice()),
                                    )),
                                    span: self.invocation_span,
                                }
                                .alloc_on(self.ast),
                            );
                        }
                        Piece::Argument(index) => {
                            args.push(self.args[index + 2]);
                        }
                    }
                }

                let child = MacroExpander::new(
                    self.ast,
                    self.global_ctx.clone(),
                    self.invocation_span,
                    wrapper,
                    args,
                );
                child.expand()
            }
            BuiltinMacroKind::Bind => {
                if self.args.is_empty() {
                    return Err(CodeDiagnostic::NotEnoughMacroArguments(1))
                        .with_span(self.invocation_span);
                }

                let (bindee, prev_bound_args) = macro_arg!(self, 0);
                let mut new_args: Vec<_> = prev_bound_args.to_vec();
                new_args.extend(self.args.iter().copied().skip(1));

                let bound_args = self.ast.arena.alloc_slice_copy(&new_args[..]);

                Ok(Expr {
                    kind: ExprKind::Macro(bindee, bound_args),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::Reduce => {
                if self.args.len() < 2 {
                    return Err(CodeDiagnostic::NotEnoughMacroArguments(2))
                        .with_span(self.invocation_span);
                }

                let (f, bound_args) = macro_arg!(self, 0);
                let mut expr = self.args[1];

                for arg in self.args.iter().skip(2) {
                    let mut new_args: Vec<_> = bound_args.to_vec();
                    new_args.push(expr);
                    new_args.push(arg);
                    let child = MacroExpander::new(
                        self.ast,
                        self.global_ctx.clone(),
                        self.invocation_span,
                        f,
                        new_args,
                    );
                    expr = child.expand()?;
                }

                Ok(expr)
            }
            BuiltinMacroKind::Cfg => {
                assert_args!(self, 1);
                let name = string_arg!(self, 0);

                Ok(Expr {
                    kind: ExprKind::Lit(Lit::Bool(
                        self.global_ctx.has_cfg(std::str::from_utf8(name).unwrap()),
                    )),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
        }
    }
}
