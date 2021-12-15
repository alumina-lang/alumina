use std::path::PathBuf;
use std::process::Command;
use std::{env, iter::once};

use quote::{format_ident, quote};
use serde::Deserialize;
use serde_json::from_reader;
use std::fs::File;
use std::io::Write;
use syn::{parse_quote, TraitItem};

#[derive(Deserialize)]
struct Node {
    r#type: String,
    named: bool,
}

fn sanitize_identifier(name: &str) -> String {
    let mut result = String::with_capacity(name.len());
    for c in name.chars() {
        if ('a'..='z').contains(&c)
            || ('A'..='Z').contains(&c)
            || ('0'..='9').contains(&c)
            || c == '_'
        {
            result.push(c);
        } else {
            let replacement = match c {
                '~' => "TILDE",
                '`' => "BQUOTE",
                '!' => "BANG",
                '@' => "AT",
                '#' => "POUND",
                '$' => "DOLLAR",
                '%' => "PERCENT",
                '^' => "CARET",
                '&' => "AMP",
                '*' => "STAR",
                '(' => "LPAREN",
                ')' => "RPAREN",
                '-' => "DASH",
                '+' => "PLUS",
                '=' => "EQ",
                '{' => "LBRACE",
                '}' => "RBRACE",
                '[' => "LBRACK",
                ']' => "RBRACK",
                '\\' => "BSLASH",
                '|' => "PIPE",
                ':' => "COLON",
                ';' => "SEMI",
                '"' => "DQUOTE",
                '\'' => "SQUOTE",
                '<' => "LT",
                '>' => "GT",
                ',' => "COMMA",
                '.' => "DOT",
                '?' => "QMARK",
                '/' => "SLASH",
                '\n' => "LF",
                '\r' => "CR",
                '\t' => "TAB",
                _ => continue,
            };
            if !result.is_empty() && !result.ends_with('_') {
                result.push('_');
            }
            result += replacement;
        }
    }
    result
}

fn generate_visitor(filename: PathBuf) -> String {
    let file = File::open(filename).unwrap();
    let parsed: Vec<Node> = from_reader(file).expect("could not parse the node types JSON");

    let (trait_fns, match_arms): (Vec<_>, Vec<_>) = parsed
        .into_iter()
        .filter(|node| node.named)
        .chain(once(Node {
            r#type: "ERROR".to_string(),
            named: true,
        }))
        .map(|symbol| {
            let raw_name = &symbol.r#type;
            let sanitized_name = sanitize_identifier(&symbol.r#type);
            let method_name = format_ident!("visit_{}", sanitized_name);
            let doc_name = format!("{:?}", raw_name).replace('`', "\\`");
            let doc_string = format!("Visits a node of type `{}`", doc_name);

            let trait_fn: TraitItem = parse_quote! {
                #[doc=#doc_string]
                #[allow(non_snake_case)]
                #[allow(unused_variables)]
                fn #method_name(&mut self, node: ::tree_sitter::Node<'tree>) -> Self::ReturnType {
                    unimplemented!(#sanitized_name)
                }
            };

            let match_arm = quote! {
                #raw_name => self.#method_name(node)
            };

            (trait_fn, match_arm)
        })
        .unzip();

    let return_item: TraitItem = parse_quote! {
        type ReturnType;
    };

    let dispatch_visit_fn: TraitItem = parse_quote! {
        #[doc=r"Visits a node of any type."]
        fn visit(&mut self, node: ::tree_sitter::Node<'tree>) -> Self::ReturnType {
            match node.kind() {
                #(#match_arms,)*
                _ => panic!("unknown node kind: {}", node.kind())
            }
        }
    };

    let output = quote! {
        extern "C" {
            fn tree_sitter_alumina() -> tree_sitter::Language;
        }

        pub fn language() -> tree_sitter::Language {
            unsafe { tree_sitter_alumina() }
        }

        pub trait AluminaVisitor<'tree>: Sized {
            #return_item
            #dispatch_visit_fn
            #(#trait_fns)*
        }
    };

    output.to_string()
}

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let grammar_path = manifest_dir.join("grammar.js");
    let result = Command::new("tree-sitter")
        .current_dir(&out_dir)
        .arg("generate")
        .arg("--no-bindings")
        .arg(&grammar_path)
        .status()
        .unwrap();

    if !result.success() {
        panic!("failed to generate the grammar");
    }

    let src_dir = out_dir.join("src");
    let parser_path = src_dir.join("parser.c");
    let mut c_config = cc::Build::new();

    c_config.include(&src_dir);
    c_config
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-trigraphs");
    c_config.file(&parser_path);
    c_config.compile("parser");

    let parser_file = out_dir.join("parser.rs");
    let node_types = src_dir.join("node-types.json");

    let visitor = generate_visitor(node_types);
    File::create(parser_file)
        .unwrap()
        .write_all(visitor.as_bytes())
        .unwrap();

    println!("cargo:rerun-if-changed=grammar.js");
}
