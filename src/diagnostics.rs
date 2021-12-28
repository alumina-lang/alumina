use std::{cell::RefCell, collections::HashMap, path::PathBuf, rc::Rc};

use colored::Colorize;

use crate::common::{AluminaError, CodeError, FileId, Marker};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Level {
    Error = 0,
    Warning = 1,
    #[allow(dead_code)]
    Note = 2,
}

struct DiagnosticContextInner {
    file_map: HashMap<FileId, PathBuf>,
    messages: Vec<(Level, CodeError)>,
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
                file_map: HashMap::new(),
                messages: Vec::new(),
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
        self.inner.borrow_mut().messages.push((Level::Error, err));
    }

    pub fn add_warning(&self, err: CodeError) {
        self.inner.borrow_mut().messages.push((Level::Warning, err));
    }

    #[allow(dead_code)]
    pub fn add_note(&self, err: CodeError) {
        self.inner.borrow_mut().messages.push((Level::Note, err));
    }

    pub fn print_error_report(&self) -> Result<(), AluminaError> {
        let inner = self.inner.borrow();
        let mut all_errors: Vec<_> = inner.messages.clone();
        all_errors.sort_by_key(|(_level, err)| {
            err.backtrace
                .iter()
                .filter_map(|m| match m {
                    Marker::Span(span) => Some((span.file, span.start)),
                    _ => None,
                })
                .last()
        });

        let mut file_cache = HashMap::new();

        for (level, error) in all_errors {
            let level = match level {
                Level::Error => "error".red(),
                Level::Warning => "warning".yellow(),
                Level::Note => "note".green(),
            };

            let tagline = format!("{}: {}", level, error.kind).bold();
            eprintln!("{}", tagline);

            // An error can happen deep inside the code that we didn't write because most of the typechecking
            // happens during or after monomorphization.
            let mut skip = false;
            for frame in error.backtrace {
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
                    let source = file_cache
                        .entry(span.file)
                        .or_insert_with(|| std::fs::read_to_string(file_name).unwrap());

                    let (line, column) = line_and_column(source, span.start);
                    eprintln!(" --> {}:{}:{}", file_name.display(), line, column,);
                } else {
                    eprintln!(" --> {{ unresolved location }}");
                }
            }

            eprintln!();
        }

        Ok(())
    }
}

pub fn line_and_column(source: &str, byte_offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut column = 1;
    for (i, c) in source.chars().enumerate() {
        if i == byte_offset {
            break;
        }
        if c == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    (line, column)
}
