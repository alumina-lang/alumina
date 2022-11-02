use crate::common::{AluminaError, CodeError, CodeErrorKind, FileId, HashMap, IndexSet, Marker};

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

struct DiagnosticContextInner {
    file_map: HashMap<FileId, PathBuf>,
    messages: IndexSet<(Level, CodeError)>,
    counter: usize,
}

#[derive(Clone)]
pub struct DiagnosticContext {
    inner: Rc<RefCell<DiagnosticContextInner>>,
}

impl DiagnosticContext {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(DiagnosticContextInner {
                file_map: HashMap::default(),
                messages: Default::default(),
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
        self.inner
            .borrow_mut()
            .messages
            .insert((Level::Warning, err));
    }

    pub fn add_note(&self, err: CodeError) {
        self.inner.borrow_mut().messages.insert((Level::Note, err));
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

        for (level, error) in all_errors {
            let level = match level {
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
                continue;
            }

            let tagline = format!("{}: {}", level, error.kind).bold();
            eprintln!("{}", tagline);

            // An error can happen deep inside the code that we didn't write because most of the typechecking
            // happens during or after monomorphization.
            let mut skip = false;
            let mut has_backtrace = false;
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
                        " --> {}:{}:{}",
                        file_name.display(),
                        span.line + 1,
                        span.column + 1
                    );
                } else {
                    eprintln!(" --> {{ unresolved location }}");
                }
                has_backtrace = true;
            }

            if let CodeErrorKind::InternalError(_, backtrace) = &error.kind {
                eprintln!();
                eprintln!("Compiler backtrace:");
                eprintln!("{:?}", backtrace);
                has_backtrace = true;
            }

            if has_backtrace {
                eprintln!();
            }
        }

        Ok(())
    }
}
