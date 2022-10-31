use crate::ast::Span;
use crate::common::{AluminaError, CodeError, CodeErrorKind, FileId, Marker};

use once_cell::unsync::OnceCell;

use std::marker::PhantomData;

use tree_sitter::{Query, QueryCursor};

include!(concat!(env!("OUT_DIR"), "/parser.rs"));

static ERROR_QUERY: once_cell::sync::OnceCell<Query> = once_cell::sync::OnceCell::new();

pub struct ParseCtx<'src> {
    source: String,
    tree: OnceCell<tree_sitter::Tree>,
    file_id: FileId,
    _phantom: PhantomData<&'src ()>,
}

impl<'src> ParseCtx<'src> {
    pub fn from_source(file_id: FileId, source: String) -> Self {
        ParseCtx {
            source,
            tree: OnceCell::new(),
            file_id,
            _phantom: PhantomData,
        }
    }

    pub fn source(&'src self) -> &'src str {
        &self.source
    }

    pub fn file_id(&self) -> FileId {
        self.file_id
    }

    pub fn root_node(&'src self) -> tree_sitter::Node<'src> {
        match self.tree.get() {
            Some(tree) => tree.root_node(),
            None => {
                let mut parser = tree_sitter::Parser::new();
                parser.set_language(language()).unwrap();

                self.tree
                    .set(parser.parse(self.source.as_str(), None).unwrap())
                    .unwrap();
                self.root_node()
            }
        }
    }

    pub fn check_syntax_errors(
        &'src self,
        node: tree_sitter::Node<'src>,
    ) -> Result<(), AluminaError> {
        if !node.has_error() {
            return Ok(());
        }

        let mut cursor = QueryCursor::new();
        let query = ERROR_QUERY.get_or_init(|| Query::new(language(), "(ERROR) @node").unwrap());

        let matches = cursor.matches(query, node, self.source.as_bytes());
        let mut errors = Vec::new();
        for m in matches {
            let error_node = m.nodes_for_capture_index(0).next().unwrap();
            errors.push(CodeError {
                kind: CodeErrorKind::ParseError(self.node_text(error_node).to_string()),
                backtrace: vec![Marker::Span(Span {
                    start: error_node.start_byte(),
                    end: error_node.end_byte(),
                    line: error_node.start_position().row,
                    column: error_node.start_position().column,
                    file: self.file_id,
                })],
            })
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(AluminaError::CodeErrors(errors))
        }
    }

    pub fn node_text(&'src self, node: tree_sitter::Node<'src>) -> &'src str {
        &self.source[node.byte_range()]
    }
}
