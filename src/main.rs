#![feature(assert_matches)]

mod common;
mod context;
mod name_resolution;
mod parser;
mod types;
mod utils;
mod visitors;

use common::SyntaxError;
use parser::ParseCtx;
use types::{Field, Struct, Symbol, SymbolP};
use visitors::types::TypeVisitor;

use crate::context::GlobalCtx;
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::AluminaVisitor;
use crate::visitors::pass1::FirstPassVisitor;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
// const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

struct TypeMaker<'gcx> {
    types: Vec<SymbolP<'gcx>>,
}

impl<'gcx> TypeMaker<'gcx> {
    pub fn new() -> Self {
        Self { types: Vec::new() }
    }

    fn make_struct<'src>(
        &mut self,
        symbol: SymbolP<'gcx>,
        _node: tree_sitter::Node<'src>,
        scope: Scope<'gcx, 'src>,
    ) -> Result<(), SyntaxError<'src>> {
        let mut placeholders: Vec<SymbolP<'gcx>> = Vec::new();
        let mut fields: Vec<Field<'gcx>> = Vec::new();

        let parse_ctx = scope.parse_ctx().unwrap();

        for (_name, item) in scope
            .0
            .borrow()
            .items
            .iter()
            .flat_map(|(k, v)| v.iter().map(|vv| (*k, vv)))
        {
            match item {
                Item::Placeholder(placeholder) => {
                    placeholders.push(*placeholder);
                }
                Item::Field(field_ref, node) => {
                    let mut visitor = TypeVisitor::new(scope.clone());
                    let field_type = visitor.visit(node.child_by_field_name("type").unwrap())?;

                    fields.push(Field {
                        symbol: *field_ref,
                        ty: field_type,
                    });
                }
                _ => {}
            }
        }

        let result = Symbol::Struct(Struct {
            placeholders: parse_ctx.alloc_slice(placeholders.as_slice()),
            fields: parse_ctx.alloc_slice(fields.as_slice()),
        });

        symbol.assign(result);

        self.types.push(symbol);

        Ok(())
    }

    pub fn make_named_types<'src>(
        &mut self,
        scope: Scope<'gcx, 'src>,
    ) -> Result<(), SyntaxError<'src>> {
        for item in scope.0.borrow().items.values().flat_map(|f| f.iter()) {
            match item {
                Item::Module(module) => {
                    self.make_named_types(module.clone());
                }
                Item::Type(symbol, node, scope) => match node.kind() {
                    "struct_definition" => self.make_struct(*symbol, *node, scope.clone())?,
                    _ => unimplemented!(),
                },
                _ => {}
            }
        }

        Ok(())
    }
}

struct CompilationUnit {
    source: String,
    name: String,
}

fn compile(units: Vec<CompilationUnit>) {
    let ctx = GlobalCtx::new();

    let root_scope = Scope::new_root();
    let crate_scope = root_scope.new_child(ScopeType::Crate, "my_crate");

    root_scope
        .add_item("my_crate", Item::Module(crate_scope.clone()))
        .unwrap();

    let parse_contexts: Vec<_> = units
        .iter()
        .map(|unit| ParseCtx::from_source(&ctx, &unit.source))
        .collect();

    for (i, ctx) in parse_contexts.iter().enumerate() {
        let module_scope =
            crate_scope.new_child_with_parse_ctx(ScopeType::Module, &units[i].name, ctx.clone());

        crate_scope
            .add_item(&units[i].name, Item::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(module_scope.clone());
        visitor.visit(ctx.root_node()).unwrap();
    }

    let mut maker = TypeMaker::new();
    maker.make_named_types(crate_scope).unwrap();

    drop(parse_contexts);

    println!("{:#?}", maker.types);
}

fn main() {
    compile(vec![
        CompilationUnit {
            source: "struct a { inner: &mod2::a }".to_string(),
            name: "mod1".to_string(),
        },
        CompilationUnit {
            source: "struct a { inner: &mod1::a }".to_string(),
            name: "mod2".to_string(),
        },
        CompilationUnit {
            source: "struct a { inner: &mod1::a }".to_string(),
            name: "mod3".to_string(),
        },
    ]);
}
