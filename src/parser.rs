include!(concat!(env!("OUT_DIR"), "/parser.rs"));

pub fn parse(input: &str) -> tree_sitter::Tree {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(language()).unwrap();

    parser.parse(input, None).unwrap()
}
