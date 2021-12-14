use std::fmt::Debug;
use tree_sitter::Node;

pub struct NodeWrapper<'t>(&'t str, Node<'t>, usize);

impl<'t> NodeWrapper<'t> {
    #[allow(unused)]
    pub fn new(source: &'t str, node: Node<'t>) -> Self {
        Self(source, node, 0)
    }
}

impl Debug for NodeWrapper<'_> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let node = self.1;
        let mut cursor = node.walk();

        writeln!(fmt, "[{} {:?}]", node.kind(), &self.0[node.byte_range()])?;
        for node in self.1.children(&mut cursor) {
            let indent = " ".repeat(self.2);
            write!(fmt, "{}{:?}", indent, NodeWrapper(self.0, node, self.2 + 2))?;
        }

        Ok(())
    }
}
