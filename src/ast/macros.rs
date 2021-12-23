use std::collections::HashMap;

use once_cell::unsync::OnceCell;

use crate::{
    ast::{
        AstCtx, BuiltinMacro, BuiltinMacroKind, Expr, ExprKind, FieldInitializer, Item, ItemP, Lit,
    },
    common::{AluminaError, ArenaAllocatable, CodeErrorKind},
    diagnostics::{line_and_column, DiagnosticContext},
    name_resolution::scope::{NamedItem, Scope},
};

use super::{expressions::ExpressionVisitor, AstId, ExprP, Macro, MacroParameter, Span, Statement};

pub struct MacroMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    diag_ctx: DiagnosticContext,
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
                return Err(CodeErrorKind::CannotConstEvaluate).with_span($self.invocation_span);
            }
        }
    };
}

impl<'ast> MacroMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, diag_ctx: DiagnosticContext) -> Self {
        Self { ast, diag_ctx }
    }

    pub fn make<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
    ) -> Result<(), AluminaError> {
        use crate::common::WithSpanDuringParsing;

        if let Some(inner) = symbol.try_get() {
            match inner {
                Item::Macro(m) => {
                    if m.body.get().is_some() {
                        return Ok(());
                    } else {
                        return Err(CodeErrorKind::RecursiveMacroCall).with_span(&scope, node);
                    }
                }
                Item::BuiltinMacro(m) => {
                    return Ok(());
                }
                _ => unreachable!(),
            }
        }

        let mut parameters = Vec::new();
        let mut has_et_cetera = false;

        let code = scope.code().unwrap();
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: code.file_id(),
        };

        let is_builtin = match node.child_by_field_name("attributes") {
            Some(attribute_node) => {
                let mut cursor = attribute_node.walk();
                let result = attribute_node
                    .children(&mut cursor)
                    .any(|n| code.node_text(n.child_by_field_name("name").unwrap()) == "builtin");
                result
            }
            None => false,
        };

        if is_builtin {
            let kind = match name.unwrap() {
                "env" => BuiltinMacroKind::Env,
                "include_bytes" => BuiltinMacroKind::IncludeBytes,
                "concat" => BuiltinMacroKind::Concat,
                "line" => BuiltinMacroKind::Line,
                "column" => BuiltinMacroKind::Column,
                "file" => BuiltinMacroKind::File,
                s => {
                    return Err(CodeErrorKind::UnknownBuiltinMacro(s.to_string()))
                        .with_span(&scope, node)
                }
            };

            symbol.assign(Item::BuiltinMacro(BuiltinMacro {
                kind,
                span: Some(span),
            }));

            return Ok(());
        }

        for (_name, item) in scope.inner().all_items() {
            match item {
                NamedItem::MacroParameter(id, et_cetera) => {
                    if has_et_cetera && *et_cetera {
                        return Err(CodeErrorKind::MultipleEtCeteras).with_span(&scope, node);
                    } else if *et_cetera {
                        has_et_cetera = true;
                    }

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: code.file_id(),
                    };

                    parameters.push(MacroParameter {
                        id: *id,
                        et_cetera: *et_cetera,
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
            self.diag_ctx.clone(),
            scope.clone(),
            has_et_cetera,
        )
        .generate(node.child_by_field_name("body").unwrap())?;

        // Two-step assignment to detect recursion
        symbol.get_macro().body.set(body).unwrap();

        Ok(())
    }
}

pub struct MacroExpander<'ast> {
    ast: &'ast AstCtx<'ast>,
    diag_ctx: DiagnosticContext,

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
        diag_ctx: DiagnosticContext,
        invocation_span: Option<Span>,
        r#macro: ItemP<'ast>,
        arguments: Vec<ExprP<'ast>>,
    ) -> Self {
        Self {
            ast,
            diag_ctx,
            r#macro,
            args: arguments,
            invocation_span,
            replacements: HashMap::new(),
            id_replacements: HashMap::new(),
            et_cetera_arg: None,
            et_cetera_index: None,
        }
    }

    pub fn expand(mut self) -> Result<ExprP<'ast>, AluminaError> {
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

            let etc_args: Vec<_> = self.args[et_cetera_index..et_cetera_index + etc_count]
                .iter()
                .copied()
                .collect();

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
        use super::ExprKind::*;
        use crate::common::CodeErrorBuilder;

        let kind = match expr.kind {
            Call(callee, args) => Call(self.visit(callee)?, self.expand_args(args)?),
            Tuple(args) => Tuple(self.expand_args(args)?),
            Array(args) => Array(self.expand_args(args)?),
            DeferedMacro(item, args) => {
                let child = MacroExpander::new(
                    self.ast,
                    self.diag_ctx.clone(),
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
                    .into_iter()
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
            RangeIndex(inner, lower, upper) => RangeIndex(
                self.visit(inner)?,
                lower.map(|i| self.visit(i)).transpose()?,
                upper.map(|i| self.visit(i)).transpose()?,
            ),
            If(condition, then, els) => {
                If(self.visit(condition)?, self.visit(then)?, self.visit(els)?)
            }
            Cast(inner, typ) => Cast(self.visit(inner)?, typ),
            Continue | EnumValue(_, _) | Lit(_) | Void | Fn(_, _) | Static(_) | Const(_) => {
                expr.kind.clone()
            }
        };

        let result = Expr {
            kind,
            span: self.invocation_span,
        };

        Ok(result.alloc_on(self.ast))
    }

    fn visit_stmt(&mut self, stmt: &Statement<'ast>) -> Result<Statement<'ast>, AluminaError> {
        use super::StatementKind::*;

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

                let value = match std::str::from_utf8(name).map(|n| std::env::var(n)) {
                    Ok(Ok(v)) => self.ast.arena.alloc_slice_copy(v.as_bytes()),
                    _ => return Err(CodeErrorKind::InternalError).with_span(self.invocation_span),
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
                    .and_then(|s| {
                        self.diag_ctx.get_file_path(s.file).map(|filename| {
                            line_and_column(&std::fs::read_to_string(filename).unwrap(), s.start)
                        })
                    })
                    .ok_or(CodeErrorKind::NoSpanInformation)
                    .with_span(self.invocation_span)?;

                let kind = if let BuiltinMacroKind::Line = kind {
                    ExprKind::Lit(Lit::Int(line as u128, None))
                } else {
                    ExprKind::Lit(Lit::Int(column as u128, None))
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
                        self.diag_ctx.get_file_path(s.file).map(|filename| {
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
                assert_args!(self, 1);
                todo!()
            }
            BuiltinMacroKind::Concat => {
                let parts =
                    self.args
                        .iter()
                        .map(|arg| match arg.kind {
                            ExprKind::Lit(Lit::Str(s)) => Ok(s),
                            _ => Err(CodeErrorKind::CannotConstEvaluate)
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
        }
    }
}
