use crate::ast::Span;
use crate::common::{
    AluminaError, CodeDiagnostic, CodeError, FileId, HashMap, HashSet, IndexSet, Marker,
};
use crate::ir::const_eval::ConstEvalErrorKind;
use alumina_boot_macros::AstSerializable;
use colored::Colorize;

use std::backtrace::Backtrace;
use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use serde::Serialize;

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum Level {
    Error = 2,
    Warning = 1,
    #[allow(dead_code)]
    Note = 0,
}

#[derive(Debug, Clone, Copy, AstSerializable)]
pub enum Action {
    Keep,
    Allow,
    Deny,
}

#[derive(Debug, Clone, AstSerializable)]
pub struct Override {
    pub span: Option<Span>,
    pub kind: Option<String>,
    pub action: Action,
}

#[derive(Debug, Clone)]
pub struct LocationOverride {
    pub span: Span,

    pub new_file: FileId,
    pub new_line: usize,
}

struct DiagnosticContextInner {
    file_map: HashMap<FileId, PathBuf>,
    messages: IndexSet<(Level, CodeError)>,
    location_overrides: HashMap<FileId, Vec<LocationOverride>>,
    hidden_spans: HashSet<Span>,
    overrides: Vec<Override>,
    counter: usize,
}

struct DiagNode {
    marker: Marker,
    parent: Option<Rc<DiagNode>>,
}

#[derive(Clone)]
pub struct DiagnosticsStack {
    diag_ctx: DiagnosticContext,
    tail: Rc<RefCell<Rc<DiagNode>>>,
}

#[derive(Default)]
pub struct DiagnosticsStackGuard {
    stack: Option<DiagnosticsStack>,
}

impl Drop for DiagnosticsStackGuard {
    fn drop(&mut self) {
        if let Some(stack) = self.stack.take() {
            stack.pop();
        }
    }
}

impl DiagnosticsStack {
    pub fn new(diag_ctx: DiagnosticContext) -> Self {
        Self {
            diag_ctx,
            tail: Rc::new(RefCell::new(Rc::new(DiagNode {
                marker: Marker::Root,
                parent: None,
            }))),
        }
    }

    pub fn pop(&self) {
        let mut tail = self.tail.borrow_mut();

        let new_tail = Rc::clone(tail.parent.as_ref().unwrap());
        *tail = new_tail;
    }

    pub fn overflow_check(&self) -> Result<(), AluminaError> {
        // calculate the length of the backtrace
        let mut tail = self.tail.borrow_mut().clone();
        let mut len = 0;
        while let Some(ref parent) = tail.parent {
            len += 1;
            tail = parent.clone();
        }

        if len > 1000 {
            return Err(AluminaError::CodeErrors(vec![CodeError {
                kind: CodeDiagnostic::InternalError(
                    "backtrace overflow".into(),
                    Backtrace::capture().into(),
                ),
                backtrace: self.materialize(),
            }]));
        }

        Ok(())
    }

    pub fn push(&self, marker: Marker) -> DiagnosticsStackGuard {
        let mut tail = self.tail.borrow_mut();

        let new_tail = Rc::new(DiagNode {
            marker,
            parent: Some(Rc::clone(&*tail)),
        });

        *tail = new_tail;

        DiagnosticsStackGuard {
            stack: Some(self.clone()),
        }
    }

    fn materialize(&self) -> Vec<Marker> {
        let mut tail = self.tail.borrow_mut().clone();

        let mut markers = vec![];
        while let Some(ref parent) = tail.parent {
            markers.push(tail.marker.clone());
            tail = parent.clone();
        }

        //markers.reverse();
        markers
    }

    pub fn err(&self, kind: CodeDiagnostic) -> AluminaError {
        AluminaError::CodeErrors(vec![CodeError {
            kind,
            backtrace: self.materialize(),
        }])
    }

    pub fn warn(&self, kind: CodeDiagnostic) {
        self.diag_ctx.add_warning(CodeError {
            kind,
            backtrace: self.materialize(),
        });
    }

    pub fn note(&self, kind: CodeDiagnostic) {
        self.diag_ctx.add_note(CodeError {
            kind,
            backtrace: self.materialize(),
        });
    }

    pub fn push_span(&self, span: Option<Span>) -> DiagnosticsStackGuard {
        if let Some(span) = span {
            self.push(Marker::Span(span))
        } else {
            DiagnosticsStackGuard::default()
        }
    }

    pub fn fork(&self) -> DiagnosticsStack {
        DiagnosticsStack {
            diag_ctx: self.diag_ctx.clone(),
            tail: Rc::new(RefCell::new(Rc::clone(&*self.tail.borrow()))),
        }
    }
}

#[derive(Serialize)]
pub struct Location {
    pub file: String,
    pub line: usize,
    pub column: Option<usize>,
}

#[derive(Serialize)]
pub struct Diagnostic {
    pub level: Level,
    pub kind: String,
    pub message: String,
    pub backtrace: Vec<Option<Location>>,
}

#[derive(Clone)]
pub struct DiagnosticContext {
    inner: Rc<RefCell<DiagnosticContextInner>>,
}

impl Default for DiagnosticContext {
    fn default() -> Self {
        Self::new()
    }
}

impl DiagnosticContext {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(DiagnosticContextInner {
                file_map: HashMap::default(),
                messages: Default::default(),
                location_overrides: Default::default(),
                hidden_spans: Default::default(),
                overrides: Default::default(),
                counter: 0,
            })),
        }
    }

    pub fn get_file_path(&self, file_id: FileId) -> Option<PathBuf> {
        self.inner.borrow().file_map.get(&file_id).cloned()
    }

    pub fn make_file_id(&self) -> FileId {
        let mut inner = self.inner.borrow_mut();
        let file_id = FileId { id: inner.counter };
        inner.counter += 1;
        file_id
    }

    pub fn add_file(&self, file_id: FileId, source_file: PathBuf) {
        let mut inner = self.inner.borrow_mut();
        inner.file_map.insert(file_id, source_file);
    }

    pub fn add_override(&self, r#override: Override) {
        self.inner.borrow_mut().overrides.push(r#override);
    }

    pub fn add_hidden_span(&self, span: Span) {
        self.inner.borrow_mut().hidden_spans.insert(span);
    }

    pub fn add_location_override(&self, span: Span, new_file: PathBuf, new_line: usize) {
        let mut inner = self.inner.borrow_mut();

        let new_file_id = match inner
            .file_map
            .iter()
            .find(|(_, v)| v == &&new_file)
            .map(|(k, _)| *k)
        {
            Some(file_id) => file_id,
            None => {
                let file_id = FileId { id: inner.counter };
                inner.counter += 1;
                inner.file_map.insert(file_id, new_file);
                file_id
            }
        };

        inner
            .location_overrides
            .entry(span.file)
            .or_default()
            .push(LocationOverride {
                span,
                new_file: new_file_id,
                new_line,
            });
    }

    pub fn map_span(&self, mut span: Span) -> Span {
        let inner = self.inner.borrow();
        let Some(overrides) = inner.location_overrides.get(&span.file) else {
            return span;
        };

        let mut innermost_override = None;

        for r#override in overrides {
            if r#override.span.contains(&span) {
                match innermost_override {
                    None => {
                        innermost_override = Some(r#override);
                    }
                    Some(innermost) => {
                        if innermost.span.contains(&r#override.span) {
                            innermost_override = Some(r#override);
                        }
                    }
                }
            }
        }

        if let Some(r#override) = innermost_override {
            span.file = r#override.new_file;
            span.line = ((span.line as isize - r#override.span.line as isize)
                + r#override.new_line as isize)
                .max(0) as usize;

            // Columns cannot really be mapped, so just drop them.
            span.column = None;
        }

        span
    }

    pub fn overrides(&self) -> Vec<Override> {
        self.inner.borrow().overrides.clone()
    }

    pub fn add_from_error(&self, err: AluminaError) -> Result<(), AluminaError> {
        match err {
            AluminaError::CodeErrors(errors) => {
                for e in errors {
                    self.add_error(e);
                }
            }
            _ => return Err(err),
        }
        Ok(())
    }

    pub fn add_error(&self, err: CodeError) {
        self.inner.borrow_mut().messages.insert((Level::Error, err));
    }

    pub fn add_warning(&self, err: CodeError) {
        let mut inner = self.inner.borrow_mut();

        let mut min_span_length = None;
        let mut action = Action::Keep;

        let error_span = err
            .backtrace
            .iter()
            .filter_map(|v| match v {
                Marker::Span(s) => Some(s),
                _ => None,
            })
            .copied()
            .next();

        for r#override in &inner.overrides {
            // Lint name has to match
            if r#override.kind.is_some() && r#override.kind.as_deref() != Some(err.kind.as_ref()) {
                continue;
            }

            // The override with the most specific (shortest) span that encloses the warning
            // wins. Global overrides (no span) are always overridden by local ones.
            if let Some(override_span) = r#override.span {
                if let Some(error_span) = error_span {
                    if !override_span.contains(&error_span) {
                        continue;
                    }
                } else {
                    continue;
                }

                if override_span.len() < min_span_length.unwrap_or(usize::MAX) {
                    min_span_length = Some(override_span.len());
                } else {
                    continue;
                }
            } else if min_span_length.is_some() {
                continue;
            }

            action = r#override.action;
        }

        match action {
            Action::Keep => {
                inner.messages.insert((Level::Warning, err));
            }
            Action::Allow => {}
            Action::Deny => {
                inner.messages.insert((Level::Error, err));
            }
        }
    }

    pub fn add_note(&self, err: CodeError) {
        self.inner.borrow_mut().messages.insert((Level::Note, err));
    }

    pub fn has_errors(&self) -> bool {
        self.inner
            .borrow()
            .messages
            .iter()
            .any(|(level, _)| *level == Level::Error)
    }

    /// Prints a human readable diagnostic report to stderr
    pub fn print_report(&self) -> Result<(), AluminaError> {
        let inner = self.inner.borrow();
        let mut all_errors: Vec<_> = inner.messages.iter().collect();
        all_errors.sort_by_key(|(level, err)| {
            err.backtrace
                .iter()
                .filter_map(|m| match m {
                    Marker::Span(span) => Some((*level, Some((span.file, span.start)))),
                    _ => None,
                })
                .last()
                .unwrap_or((*level, None))
        });

        let mut kinds = HashSet::default();

        for (level, error) in all_errors {
            let level_string = match level {
                Level::Error => "error".red(),
                Level::Warning => "warning".yellow(),
                Level::Note => "note".green(),
            };

            /*

            if let CodeError {
                kind: CodeDiagnostic::LocalWithUnknownType,
                ..
            } = error
            {
                // This usually means that something before the error failed, so it's just noise.
                continue;
            }


            */

            let tagline = format!("{}: {}", level_string, error.kind).bold();
            eprintln!("{}", tagline);

            // An error can happen deep inside the code that we didn't write because most of the typechecking
            // happens during or after monomorphization.
            let mut needs_padding = false;
            let mut filtered_frames = vec![];

            for frame in &error.backtrace {
                match frame {
                    Marker::Span(i) => {
                        if let Some(Marker::Span(last)) = filtered_frames.last_mut() {
                            if last.contains(i) {
                                *last = *i;
                                continue;
                            } else if i.contains(last) {
                                continue;
                            }
                        }
                    }
                    _ => {}
                };

                filtered_frames.push(frame.clone());
            }

            for marker in filtered_frames {
                let Marker::Span(span) = marker else { continue };
                if inner.hidden_spans.iter().any(|s| s.contains(&span)) {
                    continue;
                }
                let span = self.map_span(span);

                if let Some(file_name) = inner.file_map.get(&span.file) {
                    match span.column {
                        Some(column) => {
                            eprintln!(
                                "  --> {}:{}:{}",
                                file_name.display(),
                                span.line + 1,
                                column + 1
                            );
                        }
                        None => {
                            eprintln!("  --> {}:{}", file_name.display(), span.line + 1);
                        }
                    }
                } else {
                    eprintln!("  --> {{ unknown location }}");
                }
                needs_padding = true;
            }

            let is_first_of_kind = kinds.insert((*level, error.kind.as_ref()));
            if *level == Level::Warning && is_first_of_kind {
                eprintln!();
                eprintln!(
                    "  {} ignore with `#[allow({})]`",
                    "note:".bold(),
                    error.kind.as_ref()
                );
                needs_padding = true;
            }

            match &error.kind {
                CodeDiagnostic::InternalError(_, backtrace)
                | CodeDiagnostic::CannotConstEvaluate(ConstEvalErrorKind::CompilerBug(backtrace)) =>
                {
                    eprintln!();
                    eprintln!("Compiler backtrace:");
                    eprintln!("{}", backtrace);
                    needs_padding = true;
                }
                _ => {}
            }

            if needs_padding {
                eprintln!();
            }
        }

        Ok(())
    }

    /// Creates a serializable report of all errors and warnings
    pub fn create_report(&self) -> Result<Vec<Diagnostic>, AluminaError> {
        let inner = self.inner.borrow();
        let mut all_errors: Vec<_> = inner.messages.iter().collect();
        all_errors.sort_by_key(|(level, err)| {
            err.backtrace
                .iter()
                .filter_map(|m| match m {
                    Marker::Span(span) => Some((*level, Some((span.file, span.start)))),
                    _ => None,
                })
                .last()
                .unwrap_or((*level, None))
        });

        let mut diagnostics = Vec::new();
        for (level, error) in all_errors {
            let message = error.kind.to_string();

            let mut filtered_frames = vec![];
            for frame in &error.backtrace {
                match frame {
                    Marker::Span(i) => {
                        if let Some(Marker::Span(last)) = filtered_frames.last_mut() {
                            if last.contains(i) {
                                *last = *i;
                                continue;
                            } else if i.contains(last) {
                                continue;
                            }
                        }
                    }
                    _ => {}
                };
                filtered_frames.push(frame.clone());
            }

            let mut backtrace = vec![];
            for marker in filtered_frames {
                let Marker::Span(span) = marker else { continue };
                if inner.hidden_spans.iter().any(|s| s.contains(&span)) {
                    continue;
                }
                let span = self.map_span(span);

                if let Some(file_name) = inner.file_map.get(&span.file) {
                    backtrace.push(Some(Location {
                        file: file_name.display().to_string(),
                        line: span.line + 1,
                        column: span.column.map(|c| c + 1),
                    }));
                } else {
                    backtrace.push(None);
                }
            }

            diagnostics.push(Diagnostic {
                level: *level,
                kind: error.kind.as_ref().to_string(),
                message,
                backtrace,
            });
        }

        Ok(diagnostics)
    }
}
