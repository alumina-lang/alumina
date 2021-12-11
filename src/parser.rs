use std::marker::PhantomData;

use once_cell::unsync::OnceCell;

use crate::common::FileId;

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

    pub fn node_text(&'src self, node: tree_sitter::Node<'src>) -> &'src str {
        &self.source[node.byte_range()]
    }
}
