use crate::ast::Span;
use crate::common::{AluminaError, CodeError, CodeErrorKind, FileId, Marker};

use once_cell::unsync::OnceCell;

use std::marker::PhantomData;

use tree_sitter_traversal::{traverse, Order};

include!(concat!(env!("OUT_DIR"), "/parser.rs"));

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
        let mut errors = Vec::new();

        for node in traverse(node.walk(), Order::Pre) {
            if node.is_error() {
                errors.push(CodeError {
                    kind: CodeErrorKind::ParseError(self.node_text(node).to_string()),
                    backtrace: vec![Marker::Span(Span::from_node(self.file_id, node))],
                })
            } else if node.is_missing() {
                errors.push(CodeError {
                    kind: CodeErrorKind::ParseErrorMissing(node.kind().to_string()),
                    backtrace: vec![Marker::Span(Span::from_node(self.file_id, node))],
                })
            }
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
