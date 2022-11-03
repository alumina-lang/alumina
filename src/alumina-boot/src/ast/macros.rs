use crate::ast::expressions::ExpressionVisitor;
use crate::ast::lang::LangItemKind;
use crate::ast::{
    AstCtx, AstId, Attribute, BuiltinMacro, BuiltinMacroKind, Expr, ExprKind, ExprP,
    FieldInitializer, FnKind, Item, ItemP, Lit, Macro, MacroParameter, Span, Statement,
};
use crate::common::{ice, AluminaError, ArenaAllocatable, CodeErrorKind, HashMap};
use crate::global_ctx::GlobalCtx;
use crate::name_resolution::scope::{NamedItemKind, Scope};
use crate::parser::{FieldKind, NodeExt};

use once_cell::unsync::OnceCell;

pub struct MacroMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,
}

macro_rules! assert_args {
    ($self:expr, $count:expr) => {
        if $self.args.len() != $count {
            use crate::common::CodeErrorBuilder;
            return Err(CodeErrorKind::ParamCountMismatch($count, $self.args.len()))
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
                return Err(CodeErrorKind::ConstantStringExpected).with_span($self.invocation_span);
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
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        use crate::common::WithSpanDuringParsing;

        if let Some(inner) = symbol.try_get() {
            match inner {
                Item::Macro(m) => {
                    if m.body.get().is_some() {
                        return Ok(());
                    } else {
                        return Err(CodeErrorKind::RecursiveMacroCall).with_span_from(&scope, node);
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
                "include_bytes" => BuiltinMacroKind::IncludeBytes,
                "concat" => BuiltinMacroKind::Concat,
                "line" => BuiltinMacroKind::Line,
                "column" => BuiltinMacroKind::Column,
                "file" => BuiltinMacroKind::File,
                "format_args" => BuiltinMacroKind::FormatArgs,
                s => {
                    return Err(CodeErrorKind::UnknownBuiltinMacro(s.to_string()))
                        .with_span_from(&scope, node)
                }
            };

            symbol.assign(Item::BuiltinMacro(BuiltinMacro {
                kind,
                span: Some(span),
            }));

            return Ok(());
        }

        for (_name, item) in scope.inner().all_items() {
            match item.kind {
                NamedItemKind::MacroParameter(id, et_cetera, _) => {
                    if has_et_cetera && et_cetera {
                        return Err(CodeErrorKind::MultipleEtCeteras).with_span_from(&scope, node);
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

        symbol.assign(result);

        let body = ExpressionVisitor::new_for_macro(
            self.ast,
            self.global_ctx.clone(),
            scope.clone(),
            has_et_cetera,
        )
        .generate(node.child_by_field(FieldKind::Body).unwrap())?;

        scope.check_unused_items(&self.global_ctx.diag());

        // Two-step assignment to detect recursion
        symbol.get_macro().body.set(body).unwrap();

        Ok(())
    }
}

pub struct MacroExpander<'ast> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,

    r#macro: ItemP<'ast>,
    args: Vec<ExprP<'ast>>,
    invocation_span: Option<Span>,

    replacements: HashMap<AstId, ExprP<'ast>>,
    id_replacements: HashMap<AstId, AstId>,
    et_cetera_arg: Option<(AstId, Vec<ExprP<'ast>>)>,

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
                return Err(CodeErrorKind::NotEnoughMacroArguments(
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
                return Err(CodeErrorKind::ParamCountMismatch(
                    r#macro.args.len(),
                    self.args.len(),
                ))
                .with_span(self.invocation_span);
            }

            for (i, arg) in r#macro.args.iter().enumerate() {
                self.replacements.insert(arg.id, self.args[i]);
            }
        }

        self.visit(r#macro.body.get().unwrap())
    }

    fn expand_args(&mut self, args: &[ExprP<'ast>]) -> Result<&'ast [ExprP<'ast>], AluminaError> {
        use crate::common::CodeErrorBuilder;

        let mut new_args = Vec::new();
        for arg in args {
            if let super::ExprKind::EtCetera(inner) = arg.kind {
                if self.et_cetera_index.is_some() {
                    return Err(CodeErrorKind::EtCeteraInEtCetera).with_span(arg.span);
                }
                for idx in 0..self.et_cetera_arg.as_ref().unwrap().1.len() {
                    self.et_cetera_index = Some(idx);
                    new_args.push(self.visit(inner)?);
                }
                self.et_cetera_index = None;
            } else {
                new_args.push(self.visit(arg)?);
            }
        }

        Ok(new_args.alloc_on(self.ast))
    }

    fn visit(&mut self, expr: ExprP<'ast>) -> Result<ExprP<'ast>, AluminaError> {
        use crate::ast::ExprKind::*;
        use crate::common::CodeErrorBuilder;

        let kind = match expr.kind {
            Call(callee, args) => Call(self.visit(callee)?, self.expand_args(args)?),
            Tuple(args) => Tuple(self.expand_args(args)?),
            Array(args) => Array(self.expand_args(args)?),
            DeferedMacro(item, args) => {
                let child = MacroExpander::new(
                    self.ast,
                    self.global_ctx.clone(),
                    self.invocation_span,
                    item,
                    self.expand_args(args)?.to_vec(),
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
                        return Err(CodeErrorKind::CannotEtCeteraHere).with_span(expr.span);
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
            EtCetera(_) => {
                return Err(CodeErrorKind::CannotEtCeteraHere).with_span(expr.span);
            }
            Block(statements, ret) => {
                let mut new_statements = Vec::new();
                for statement in statements {
                    new_statements.push(self.visit_stmt(statement)?);
                }
                Block(new_statements.alloc_on(self.ast), self.visit(ret)?)
            }
            Binary(op, lhs, rhs) => Binary(op, self.visit(lhs)?, self.visit(rhs)?),
            Ref(inner) => Ref(self.visit(inner)?),
            Deref(inner) => Deref(self.visit(inner)?),

            Unary(op, inner) => Unary(op, self.visit(inner)?),
            Assign(lhs, rhs) => Assign(self.visit(lhs)?, self.visit(rhs)?),
            AssignOp(op, lhs, rhs) => AssignOp(op, self.visit(lhs)?, self.visit(rhs)?),
            Loop(inner) => Loop(self.visit(inner)?),
            Break(inner) => Break(inner.map(|i| self.visit(i)).transpose()?),
            Return(inner) => Return(inner.map(|i| self.visit(i)).transpose()?),
            Defer(inner) => Defer(self.visit(inner)?),
            Field(a, name, assoc_fn) => Field(self.visit(a)?, name, assoc_fn),
            Struct(ty, inits) => {
                let inits: Vec<_> = inits
                    .iter()
                    .map(|init| {
                        self.visit(init.value).map(|value| FieldInitializer {
                            name: init.name,
                            value,
                            span: self.invocation_span,
                        })
                    })
                    .collect::<Result<_, _>>()?;

                Struct(ty, inits.alloc_on(self.ast))
            }
            TupleIndex(inner, idx) => TupleIndex(self.visit(inner)?, idx),
            Index(inner, idx) => Index(self.visit(inner)?, self.visit(idx)?),
            Range(lower, upper, inclusive) => Range(
                lower.map(|i| self.visit(i)).transpose()?,
                upper.map(|i| self.visit(i)).transpose()?,
                inclusive,
            ),
            If(condition, then, els) => {
                If(self.visit(condition)?, self.visit(then)?, self.visit(els)?)
            }
            StaticIf(cond, then, els) => StaticIf(cond, self.visit(then)?, self.visit(els)?),
            Cast(inner, typ) => Cast(self.visit(inner)?, typ),
            Continue
            | EnumValue(_, _)
            | Lit(_)
            | BoundParam(_, _, _)
            | Void
            | Fn(_, _)
            | Defered(_)
            | Static(_, _)
            | Const(_, _) => expr.kind.clone(),
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
            Expression(expr) => Expression(self.visit(expr)?),
            LetDeclaration(decl) => {
                // Local variables declared in a macro must be renamed to avoid clashes if
                // same macro is evaluated multiple times in one scope.
                let replacement = self.ast.make_id();
                self.id_replacements.insert(decl.id, replacement);

                LetDeclaration(crate::ast::LetDeclaration {
                    id: replacement,
                    typ: decl.typ,
                    value: decl.value.map(|v| self.visit(v)).transpose()?,
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
            BuiltinMacroKind::Env => {
                assert_args!(self, 1);
                let name = string_arg!(self, 0);

                let value = match std::str::from_utf8(name).map(std::env::var) {
                    Ok(Ok(v)) => self.ast.arena.alloc_slice_copy(v.as_bytes()),
                    _ => ice!("invalid UTF-8 in environment variable name"),
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
                    .map(|s| (s.line + 1, s.column + 1))
                    .ok_or(CodeErrorKind::NoSpanInformation)
                    .with_span(self.invocation_span)?;

                let kind = if let BuiltinMacroKind::Line = kind {
                    ExprKind::Lit(Lit::Int(false, line as u128, None))
                } else {
                    ExprKind::Lit(Lit::Int(false, column as u128, None))
                };

                Ok(Expr {
                    kind,
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
            BuiltinMacroKind::File => {
                assert_args!(self, 0);
                let filename = self
                    .invocation_span
                    .and_then(|s| {
                        self.global_ctx
                            .diag()
                            .get_file_path(s.file)
                            .map(|filename| {
                                self.ast
                                    .arena
                                    .alloc_slice_copy(filename.to_string_lossy().as_bytes())
                            })
                    })
                    .ok_or(CodeErrorKind::NoSpanInformation)
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
                    _ => ice!("invalid UTF-8 in filename"),
                };

                let data = std::fs::read(filename)
                    .map_err(|_| CodeErrorKind::CannotReadFile(filename.to_string()))
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
                        _ => Err(CodeErrorKind::ConstantStringExpected)
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
                if self.args.is_empty() {
                    return Err(CodeErrorKind::NotEnoughMacroArguments(1))
                        .with_span(self.invocation_span);
                }

                let fmt_string = string_arg!(self, 0);

                #[derive(PartialEq, Eq, Debug)]
                enum State {
                    Normal,
                    BraceOpen,
                    BraceClose,
                }

                let mut args = Vec::new();
                let mut string_part = Vec::new();

                let make_arg = |arg: ExprP<'ast>| {
                    let ret = Expr {
                        kind: ExprKind::Call(
                            Expr {
                                kind: ExprKind::Fn(
                                    FnKind::Normal(
                                        self.ast
                                            .lang_item(LangItemKind::FormatArg)
                                            .with_span(self.invocation_span)?,
                                    ),
                                    None,
                                ),
                                span: self.invocation_span,
                            }
                            .alloc_on(self.ast),
                            [Expr {
                                kind: ExprKind::Ref(arg),
                                span: self.invocation_span,
                            }
                            .alloc_on(self.ast)]
                            .alloc_on(self.ast),
                        ),
                        span: self.invocation_span,
                    }
                    .alloc_on(self.ast);

                    Ok::<_, AluminaError>(ret)
                };

                let mut state = State::Normal;
                let mut arg_index = 0;

                macro_rules! push_string_part {
                    () => {
                        if !string_part.is_empty() {
                            args.push(make_arg(
                                Expr {
                                    kind: ExprKind::Lit(Lit::Str(
                                        self.ast.arena.alloc_slice_copy(string_part.as_slice()),
                                    )),
                                    span: self.invocation_span,
                                }
                                .alloc_on(self.ast),
                            )?);
                            string_part.clear();
                        }
                    };
                }

                for ch in fmt_string.iter().copied() {
                    state = match state {
                        State::Normal => match ch {
                            b'{' => State::BraceOpen,
                            b'}' => State::BraceClose,
                            _ => {
                                string_part.push(ch);
                                State::Normal
                            }
                        },
                        State::BraceClose => match ch {
                            b'}' => {
                                string_part.push(ch);
                                State::Normal
                            }
                            _ => {
                                return Err(CodeErrorKind::InvalidFormatString(format!(
                                    "unexpected {:?}",
                                    ch as char
                                )))
                                .with_span(self.args[0].span);
                            }
                        },
                        State::BraceOpen => match ch {
                            b'{' => {
                                string_part.push(ch);
                                State::Normal
                            }
                            b'}' => {
                                push_string_part!();

                                if self.args.len() <= arg_index + 1 {
                                    return Err(CodeErrorKind::InvalidFormatString(
                                        "not enough arguments".to_string(),
                                    ))
                                    .with_span(self.invocation_span);
                                }

                                args.push(make_arg(self.args[arg_index + 1])?);
                                arg_index += 1;

                                State::Normal
                            }
                            _ => {
                                return Err(CodeErrorKind::InvalidFormatString(format!(
                                    "unexpected {:?}",
                                    ch as char
                                )))
                                .with_span(self.invocation_span);
                            }
                        },
                    };
                }

                if state != State::Normal {
                    return Err(CodeErrorKind::InvalidFormatString(
                        "unexpected end of format string".to_string(),
                    ))
                    .with_span(self.invocation_span);
                }

                if self.args.len() > arg_index + 1 {
                    return Err(CodeErrorKind::InvalidFormatString(
                        "too many arguments".to_string(),
                    ))
                    .with_span(self.invocation_span);
                }
                push_string_part!();

                Ok(Expr {
                    kind: ExprKind::Array(args.alloc_on(self.ast)),
                    span: self.invocation_span,
                }
                .alloc_on(self.ast))
            }
        }
    }
}
