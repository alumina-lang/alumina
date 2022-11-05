use crate::ast::Span;
use crate::common::{
    AluminaError, CodeError, CodeErrorKind, FileId, HashMap, HashSet, IndexSet, Marker,
};
use colored::Colorize;

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Level {
    Error = 2,
    Warning = 1,
    #[allow(dead_code)]
    Note = 0,
}

#[derive(Debug, Clone, Copy)]
pub enum Action {
    Keep,
    Allow,
    Deny,
}

#[derive(Debug)]
pub struct Override {
    pub span: Option<Span>,
    pub kind: Option<&'static str>,
    pub action: Action,
}

struct DiagnosticContextInner {
    file_map: HashMap<FileId, PathBuf>,
    messages: IndexSet<(Level, CodeError)>,
    overrides: Vec<Override>,
    counter: usize,
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
                overrides: Default::default(),
                counter: 0,
            })),
        }
    }

    pub fn get_file_path(&self, file_id: FileId) -> Option<PathBuf> {
        self.inner.borrow().file_map.get(&file_id).cloned()
    }

    pub fn add_file(&self, source_file: PathBuf) -> FileId {
        let mut inner = self.inner.borrow_mut();
        let file_id = FileId { id: inner.counter };
        inner.counter += 1;
        inner.file_map.insert(file_id, source_file);
        file_id
    }

    pub fn add_override(&self, r#override: Override) {
        self.inner.borrow_mut().overrides.push(r#override);
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
            if r#override.kind.is_some() && r#override.kind != Some(err.kind.as_ref()) {
                continue;
            }

            // The override with the most specific (shortest) span that encloses the warning
            // wins. Global overrides (no span) are always overridden by local ones.
            if let Some(override_span) = r#override.span {
                if let Some(error_span) = error_span {
                    if !override_span.contains(error_span) {
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

    pub fn print_error_report(&self) -> Result<(), AluminaError> {
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

            if let CodeError {
                kind: CodeErrorKind::LocalWithUnknownType,
                ..
            } = error
            {
                // This usually means that something before the error failed, so it's just noise.
                //continue;
            }

            let tagline = format!("{}: {}", level_string, error.kind).bold();
            eprintln!("{}", tagline);

            // An error can happen deep inside the code that we didn't write because most of the typechecking
            // happens during or after monomorphization.
            let mut skip = false;
            let mut needs_padding = false;
            for frame in &error.backtrace {
                let span = match (frame, skip) {
                    (Marker::Span(span), false) => {
                        skip = true;
                        span
                    }
                    (Marker::Span(_), true) => continue,
                    (Marker::Monomorphization, _) => {
                        skip = false;
                        continue;
                    }
                };

                if let Some(file_name) = inner.file_map.get(&span.file) {
                    eprintln!(
                        "  --> {}:{}:{}",
                        file_name.display(),
                        span.line + 1,
                        span.column + 1
                    );
                } else {
                    eprintln!("  --> {{ unresolved location }}");
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

            if let CodeErrorKind::InternalError(_, backtrace) = &error.kind {
                eprintln!();
                eprintln!("Compiler backtrace:");
                eprintln!("{:?}", backtrace);
                needs_padding = true;
            }

            if needs_padding {
                eprintln!();
            }
        }

        Ok(())
    }
}
