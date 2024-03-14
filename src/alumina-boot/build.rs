use itertools::Itertools;
use quote::{format_ident, quote};
use serde::Deserialize;
use serde_json::from_slice;
use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use syn::{parse_quote, TraitItem};
#[derive(Deserialize)]
struct Item {
    name: String,
    id: i32,
}

#[derive(Deserialize)]
struct LanguageInfo {
    fields: Vec<Item>,
    symbols: Vec<Item>,
}

fn sanitize_identifier(name: &str, pascal_case: bool) -> String {
    let mut result = String::with_capacity(name.len());
    let mut first_char = true;
    for c in name.chars() {
        if c.is_ascii_lowercase() || c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_' {
            if pascal_case {
                if c == '_' {
                    first_char = true;
                } else if first_char {
                    result.push(c.to_ascii_uppercase());
                    first_char = false;
                } else {
                    result.push(c);
                }
            } else {
                result.push(c);
            }
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

fn generate_visitor(language_info: LanguageInfo) -> String {
    let fields = language_info
        .fields
        .iter()
        .map(|field| {
            let name = sanitize_identifier(&field.name, true);
            let id = field.id as u16;
            let ident = format_ident!("{}", name);
            let field = quote! {
                #ident = #id,
            };
            field
        })
        .collect::<Vec<_>>();

    let mut node_kinds = Vec::new();
    let mut trait_fns = Vec::new();
    let mut match_arms = Vec::new();

    let mut id_map = HashMap::new();

    for (raw_name, ids) in language_info
        .symbols
        .into_iter()
        .map(|a| (a.name, a.id as u16))
        .into_group_map()
        .into_iter()
        .sorted_by_key(|(_, ids)| ids[0])
    {
        let enum_name = sanitize_identifier(&raw_name, true);
        let sanitized_name = sanitize_identifier(&raw_name, false);
        let method_name = format_ident!("visit_{}", sanitized_name);
        let enum_member_name = format_ident!("{}", enum_name);
        let doc_name = format!("{:?}", raw_name).replace('`', "\\`");
        let doc_string = format!("Visits a node of type `{}`", doc_name);

        let trait_fn: TraitItem = parse_quote! {
            #[doc=#doc_string]
                        #[allow(unused_variables)]
            fn #method_name(&mut self, node: ::tree_sitter::Node<'tree>) -> Self::ReturnType {
                unimplemented!(#sanitized_name)
            }
        };

        let match_arm = quote! {
            NodeKind::#enum_member_name => self.#method_name(node)
        };

        let enum_member = quote! {
            #enum_member_name,
        };

        node_kinds.push(enum_member);
        trait_fns.push(trait_fn);
        match_arms.push(match_arm);

        id_map.extend(ids.into_iter().map(|id| (id, enum_member_name.clone())));
    }

    let mut node_kind_map = Vec::new();

    let max_id = id_map.keys().copied().max().unwrap();
    for i in 0..=max_id {
        if let Some(enum_member) = id_map.get(&i) {
            node_kind_map.push(quote! {
                NodeKind::#enum_member,
            });
        } else {
            node_kind_map.push(quote! {
                NodeKind::Unknown,
            });
        }
    }

    let node_kind_map_len = node_kind_map.len();

    let return_item: TraitItem = parse_quote! {
        type ReturnType;
    };

    let dispatch_visit_fn: TraitItem = parse_quote! {
        #[doc=r"Visits a node of any type."]
        fn visit(&mut self, node: ::tree_sitter::Node<'tree>) -> Self::ReturnType {
            match node.kind_typed() {
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

        #[repr(u16)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[allow(dead_code)]
        pub enum FieldKind {
            #(#fields)*
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[allow(dead_code)]
        pub enum NodeKind {
            Unknown,
            #(#node_kinds)*
        }

        const NODE_KIND_MAP: [NodeKind; #node_kind_map_len] = [
            #(#node_kind_map)*
        ];

        pub trait NodeExt<'tree, 'a> {
            type Iterator;

            fn kind_typed(&self) -> NodeKind;
            fn child_by_field(&self, field: FieldKind) -> Option<::tree_sitter::Node<'tree>>;
            fn children_by_field(
                &self,
                field: FieldKind,
                cursor: &'a mut ::tree_sitter::TreeCursor<'tree>,
            ) -> Self::Iterator;
        }

        pub struct ChildrenIterator<'tree, 'a> {
            cursor: &'a mut ::tree_sitter::TreeCursor<'tree>,
            done: bool,
            field: FieldKind,
        }

        impl<'tree, 'a> Iterator for ChildrenIterator<'tree, 'a> {
            type Item = ::tree_sitter::Node<'tree>;

            fn next(&mut self) -> Option<Self::Item> {
                if !self.done {
                    while self.cursor.field_id() != Some(std::num::NonZeroU16::new(self.field as u16).unwrap()) {
                        if !self.cursor.goto_next_sibling() {
                            return None;
                        }
                    }
                    let result = self.cursor.node();
                    if !self.cursor.goto_next_sibling() {
                        self.done = true;
                    }
                    return Some(result);
                }
                None
            }
        }

        impl<'tree, 'a> NodeExt<'tree, 'a> for ::tree_sitter::Node<'tree> where 'tree: 'a {
            type Iterator = ChildrenIterator<'tree, 'a>;

            fn kind_typed(&self) -> NodeKind {
                unsafe {
                    *NODE_KIND_MAP.get_unchecked(self.kind_id() as usize)
                }
            }

            fn child_by_field(&self, field: FieldKind) -> Option<::tree_sitter::Node<'tree>> {
                self.child_by_field_id(field as u16)
            }

            fn children_by_field(
                &self,
                field: FieldKind,
                cursor: &'a mut ::tree_sitter::TreeCursor<'tree>,
            ) -> Self::Iterator {
                cursor.reset(*self);
                cursor.goto_first_child();
                ChildrenIterator {
                    cursor,
                    done: false,
                    field,
                }
            }
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

    let grammar_path = manifest_dir.join("../../common/grammar.js");
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

    compile_grammar(&src_dir, &parser_path);

    let language_info = get_language_info(&manifest_dir, &out_dir, &src_dir, &parser_path);
    let parser_file = out_dir.join("parser.rs");

    let visitor = generate_visitor(language_info);
    File::create(parser_file)
        .unwrap()
        .write_all(visitor.as_bytes())
        .unwrap();

    println!("cargo:rerun-if-changed={}", grammar_path.display());
    println!(
        "cargo:rustc-env=ALUMINA_BUILD_TARGET_ENV={}",
        env::var("CARGO_CFG_TARGET_ENV").unwrap()
    );
}

fn get_language_info(
    manifest_dir: &Path,
    out_dir: &Path,
    src_dir: &Path,
    parser_path: &Path,
) -> LanguageInfo {
    let dump_tool_path = manifest_dir.join("dump_lang.c");
    let dump_tool_out_path = out_dir.join("dump_lang");

    // Build the tool first
    let mut cmd = cc::Build::new()
        .include(src_dir)
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-const-variable")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-trigraphs")
        .get_compiler()
        .to_command();
    cmd.arg(parser_path)
        .arg(&dump_tool_path)
        .arg("-o")
        .arg(&dump_tool_out_path);
    assert!(cmd.status().unwrap().success());

    // Run the tool
    let output = Command::new(&dump_tool_out_path).output().unwrap();

    assert!(output.status.success());

    from_slice(&output.stdout[..]).expect("could not parse the node types JSON")
}

fn compile_grammar(src_dir: &Path, parser_path: &Path) {
    cc::Build::new()
        .include(src_dir)
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-const-variable")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-trigraphs")
        .file(parser_path)
        .compile("parser");
}
