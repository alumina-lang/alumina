use crate::ast::Span;
use crate::common::{AluminaError, CodeDiagnostic, CodeError, FileId, Marker};

use once_cell::unsync::OnceCell;

use std::iter::FusedIterator;
use std::marker::PhantomData;

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
                parser.set_language(&language()).unwrap();

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

        for node in traverse_pre(node.walk()) {
            if node.is_error() {
                errors.push(CodeError {
                    kind: CodeDiagnostic::ParseError(self.node_text(node).to_string()),
                    backtrace: vec![Marker::Span(Span::from_node(self.file_id, node))],
                })
            } else if node.is_missing() {
                errors.push(CodeError {
                    kind: CodeDiagnostic::ParseErrorMissing(node.kind().to_string()),
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

// The following code is adapted from tree-sitter-traversal by Sebastian Mendez
// and carries the following license:
//
// MIT License
//
// Copyright (c) 2021 Sebastian Mendez
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

struct PreorderTraverse<'a> {
    cursor: Option<tree_sitter::TreeCursor<'a>>,
}

impl<'a> PreorderTraverse<'a> {
    pub fn new(c: tree_sitter::TreeCursor<'a>) -> Self {
        PreorderTraverse { cursor: Some(c) }
    }
}

impl<'a> Iterator for PreorderTraverse<'a> {
    type Item = tree_sitter::Node<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let c = match self.cursor.as_mut() {
            None => {
                return None;
            }
            Some(c) => c,
        };

        // We will always return the node we were on at the start;
        // the node we traverse to will either be returned on the next iteration,
        // or will be back to the root node, at which point we'll clear out
        // the reference to the cursor
        let node = c.node();

        // First, try to go to a child or a sibling; if either succeed, this will be the
        // first time we touch that node, so it'll be the next starting node
        if c.goto_first_child() || c.goto_next_sibling() {
            return Some(node);
        }

        loop {
            // If we can't go to the parent, then that means we've reached the root, and our
            // iterator will be done in the next iteration
            if !c.goto_parent() {
                self.cursor = None;
                break;
            }

            // If we get to a sibling, then this will be the first time we touch that node,
            // so it'll be the next starting node
            if c.goto_next_sibling() {
                break;
            }
        }

        Some(node)
    }
}

impl<'a> FusedIterator for PreorderTraverse<'a> {}

fn traverse_pre(mut cursor: tree_sitter::TreeCursor<'_>) -> PreorderTraverse<'_> {
    assert!(!cursor.goto_parent());
    PreorderTraverse::new(cursor)
}
