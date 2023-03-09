use crate::common::{AluminaError, CodeErrorBuilder, CodeErrorKind};

use super::Span;

pub enum Piece {
    String(Vec<u8>),
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
        BraceClose,
    }

    let mut args = Vec::new();
    let mut string_part = Vec::new();

    let mut state = State::Normal;
    let mut arg_index = 0;

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
            State::BraceOpen => match ch {
                b'{' => {
                    string_part.push(ch);
                    State::Normal
                }
                b'}' => {
                    if !string_part.is_empty() {
                        args.push(Piece::String(std::mem::take(&mut string_part)));
                    }

                    if num_args <= arg_index {
                        return Err(CodeErrorKind::InvalidFormatString(
                            "not enough arguments".to_string(),
                        ))
                        .with_span(span);
                    }

                    args.push(Piece::Argument(arg_index));
                    arg_index += 1;

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
        };
    }

    if state != State::Normal {
        return Err(CodeErrorKind::InvalidFormatString(
            "unexpected end of format string".to_string(),
        ))
        .with_span(span);
    }

    if num_args > arg_index {
        return Err(CodeErrorKind::InvalidFormatString(
            "too many arguments".to_string(),
        ))
        .with_span(span);
    }

    if !string_part.is_empty() {
        args.push(Piece::String(std::mem::take(&mut string_part)));
    }

    Ok(args)
}
