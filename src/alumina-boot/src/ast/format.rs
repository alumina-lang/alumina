use crate::common::{AluminaError, CodeErrorBuilder, CodeErrorKind, HashSet};

use super::Span;

pub enum Piece {
    String(Vec<u8>),
    Adapter(Vec<u8>, Box<Piece>),
    Argument(usize),
}

pub fn format_args(
    span: Option<Span>,
    fmt_string: &[u8],
    num_args: usize,
) -> Result<Vec<Piece>, AluminaError> {
    #[derive(PartialEq, Eq, Debug)]
    enum State {
        Normal,
        BraceOpen,
        Index,
        Adapter,
        BraceClose,
    }

    let mut used_arguments = HashSet::default();

    let mut args = Vec::new();
    let mut string_part = Vec::new();

    let mut state = State::Normal;
    let mut arg_index = 0;

    let mut index_part = Vec::new();
    let mut adapter_part = Vec::new();

    macro_rules! push_arg {
        () => {
            let index_part = std::mem::take(&mut index_part);
            let adapter_part = std::mem::take(&mut adapter_part);

            let index = if !index_part.is_empty() {
                std::str::from_utf8(&index_part)
                    .ok()
                    .and_then(|idx| idx.parse().ok())
                    .ok_or_else(|| {
                        CodeErrorKind::InvalidFormatString(
                            "invalid argument index".to_string(),
                        )
                    })
                    .with_span(span)?
            } else {
                let idx = arg_index;
                arg_index += 1;
                idx
            };

            if !string_part.is_empty() {
                args.push(Piece::String(std::mem::take(&mut string_part)));
            }

            if num_args <= index {
                return Err(CodeErrorKind::InvalidFormatString(
                    "not enough arguments".to_string(),
                ))
                .with_span(span);
            }

            used_arguments.insert(index);

            if !adapter_part.is_empty() {
                args.push(Piece::Adapter(
                    adapter_part,
                    Box::new(Piece::Argument(index)),
                ));
            } else {
                args.push(Piece::Argument(index));
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
                    .with_span(span);
                }
            },
            State::Index => match ch {
                b'0'..=b'9' => {
                    index_part.push(ch);
                    State::Index
                }
                b':' => State::Adapter,
                b'}' => {
                    push_arg!();
                    State::Normal
                }
                _ => {
                    return Err(CodeErrorKind::InvalidFormatString(format!(
                        "unexpected {:?}",
                        ch as char
                    )))
                    .with_span(span);
                }
            },
            State::Adapter => match ch {
                b'}' => {
                    push_arg!();
                    State::Normal
                }
                _ => {
                    adapter_part.push(ch);
                    State::Adapter
                }
            },
            State::BraceOpen => match ch {
                b'{' => {
                    string_part.push(ch);
                    State::Normal
                }
                b'}' => {
                    push_arg!();
                    State::Normal
                }
                b'0'..=b'9' => {
                    index_part.push(ch);
                    State::Index
                }
                b':' => State::Adapter,
                _ => {
                    return Err(CodeErrorKind::InvalidFormatString(format!(
                        "unexpected {:?}",
                        ch as char
                    )))
                    .with_span(span);
                }
            },
        };
    }

    if state != State::Normal {
        return Err(CodeErrorKind::InvalidFormatString(
            "unexpected end of format string".to_string(),
        ))
        .with_span(span);
    }

    if num_args > used_arguments.len() {
        return Err(CodeErrorKind::InvalidFormatString(
            "unused arguments".to_string(),
        ))
        .with_span(span);
    }

    if !string_part.is_empty() {
        args.push(Piece::String(std::mem::take(&mut string_part)));
    }

    Ok(args)
}
