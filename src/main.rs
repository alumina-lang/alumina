mod common;
mod context;
mod name_resolution;
mod types;
mod utils;
mod visitors;

use crate::context::GlobalCtx;
use crate::name_resolution::scope::{Item, Scope, ScopeType};
use crate::parser::AluminaVisitor;
use crate::visitors::pass1::FirstPassVisitor;

// const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

pub mod parser {
    include!(concat!(env!("OUT_DIR"), "/parser.rs"));
}

fn main() {
    let global_ctx = GlobalCtx::new();
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(parser::language()).unwrap();

    let parsed = parser.parse(SOURCE_CODE, None).unwrap();
    let root_node = parsed.root_node();
    println!("{:#?}", utils::NodeWrapper::new(SOURCE_CODE, root_node));

    let root_scope = Scope::new();
    let module_scope = root_scope.make_child(ScopeType::Crate, "hello_world");
    root_scope
        .add_item("hello_world", Item::Module(module_scope.clone()))
        .unwrap();

    let mut visitor = FirstPassVisitor::new(&global_ctx, SOURCE_CODE, module_scope);
    visitor.visit(root_node).unwrap();

    println!("{:#?}", root_scope);
}

#[cfg(test)]
mod tests {

    use crate::{
        types::{BuiltinType, SymbolP, Ty, TyP},
        visitors::types::TypeVisitor,
    };

    use super::*;

    trait AsTyP {
        fn as_typ(&self) -> TyP<'_>;
    }

    impl AsTyP for Ty<'_> {
        fn as_typ(&self) -> TyP<'_> {
            TyP::new(self)
        }
    }

    fn parse<'tcx>(global_ctx: &'tcx GlobalCtx<'tcx>, src: &'tcx str) -> Scope<'tcx> {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(parser::language()).unwrap();

        let parsed = global_ctx.arena.alloc(parser.parse(src, None).unwrap());
        let root_node = parsed.root_node();

        let root_scope = Scope::new();
        let module_scope = root_scope.make_child(ScopeType::Crate, "test");
        root_scope
            .add_item("test", Item::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(global_ctx, src, module_scope);
        visitor.visit(root_node).unwrap();

        root_scope
    }

    fn extract_type<'tcx>(
        global_ctx: &'tcx GlobalCtx<'tcx>,
        src: &'tcx str,
        root_scope: Scope<'tcx>,
    ) -> Result<TyP<'tcx>, SyntaxError<'tcx>> {
        let (scope, node) = match &(*root_scope.0).borrow().items["test"][..] {
            [Item::Module(scope)] => match &(*scope.0).borrow().items["a"][..] {
                [Item::Type(_, _, scope)] => match &(*scope.0).borrow().items["b"][..] {
                    [Item::Field(_, node)] => {
                        (scope.clone(), node.child_by_field_name("type").unwrap())
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        let mut visitor = TypeVisitor::new(global_ctx, src, scope);
        visitor.visit(node)
    }

    #[test]
    fn test_typ_eq() {
        let ctx = GlobalCtx::new();

        let ty1 = Ty::Builtin(BuiltinType::I32);
        let ty2 = Ty::Builtin(BuiltinType::I32);

        let ptr1 = Ty::Pointer(ctx.intern(ty1));
        let ptr2 = Ty::Pointer(ctx.intern(ty2));

        let typ1 = ctx.intern(ptr1);
        let typ2 = ctx.intern(ptr2);

        assert_eq!(typ1, typ2);
    }

    fn test_parse_type(typedef: &str, expected: TyP<'_>) {
        let global_ctx = GlobalCtx::new();

        let src = global_ctx
            .arena
            .alloc_str(&format!("struct a {{ b: {}; }}", typedef));
        let root_scope = parse(&global_ctx, src);
        let result = extract_type(&global_ctx, src, root_scope).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_type_builtin() {
        test_parse_type("i32", Ty::Builtin(BuiltinType::I32).as_typ());
    }

    #[test]
    fn test_parse_type_array() {
        test_parse_type(
            "[u32; 16]",
            Ty::Array(Ty::Builtin(BuiltinType::U32).as_typ(), 16).as_typ(),
        );
    }

    #[test]
    fn test_parse_type_pointer() {
        test_parse_type(
            "&i32",
            Ty::Pointer(Ty::Builtin(BuiltinType::I32).as_typ()).as_typ(),
        );
    }

    #[test]
    fn test_parse_type_tuple() {
        test_parse_type(
            "(i32, u32)",
            Ty::Tuple(&[
                Ty::Builtin(BuiltinType::I32).as_typ(),
                Ty::Builtin(BuiltinType::U32).as_typ(),
            ])
            .as_typ(),
        );
    }

    #[test]
    fn test_referenced_type() {
        let global_ctx = GlobalCtx::new();

        let src = r"
            mod foo {
                struct bar {}
            }

            struct a {
                b: foo::bar,
            }
            ";

        let root_scope = parse(&global_ctx, src);
        let result = extract_type(&global_ctx, src, root_scope).unwrap();

        assert_eq!(result, Ty::StructOrEnum(SymbolP::new(0)).as_typ());
    }

    #[test]
    fn test_referenced_type_super() {
        let global_ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            mod goo {
                use super::bar;
            }
            struct bar {}
        }

        struct a {
            b: foo::goo::bar,
        }
        ";

        let root_scope = parse(&global_ctx, src);
        let result = extract_type(&global_ctx, src, root_scope).unwrap();

        assert_eq!(result, Ty::StructOrEnum(SymbolP::new(0)).as_typ());
    }

    #[test]
    fn test_infinite_loop_lol() {
        let global_ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            use super::bar::baz;
        }

        mod bar {
            use super::foo::baz;
        }

        struct a {
            b: foo::baz,
        }
        ";

        let root_scope = parse(&global_ctx, src);
        extract_type(&global_ctx, src, root_scope).unwrap_err();
    }

    #[test]
    fn test_referenced_type_crate() {
        let global_ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            struct bar {}
        }

        struct a {
            b: crate::foo::bar,
        }
        ";

        let root_scope = parse(&global_ctx, src);
        let result = extract_type(&global_ctx, src, root_scope).unwrap();

        assert_eq!(result, Ty::StructOrEnum(SymbolP::new(0)).as_typ());
    }

    #[test]
    fn test_referenced_type_absolute() {
        let global_ctx = GlobalCtx::new();

        let src = r"
        mod foo {
            struct bar {}
        }

        struct a {
            b: ::test::foo::bar,
        }
        ";

        let root_scope = parse(&global_ctx, src);
        let result = extract_type(&global_ctx, src, root_scope).unwrap();
        assert_eq!(result, Ty::StructOrEnum(SymbolP::new(0)).as_typ());
    }

    #[test]
    fn test_parse_complex_tuple() {
        test_parse_type(
            "(i32, [u32; 16], &i32)",
            Ty::Tuple(&[
                Ty::Builtin(BuiltinType::I32).as_typ(),
                Ty::Array(Ty::Builtin(BuiltinType::U32).as_typ(), 16).as_typ(),
                Ty::Pointer(Ty::Builtin(BuiltinType::I32).as_typ()).as_typ(),
            ])
            .as_typ(),
        );
    }

    #[test]
    fn test_parse_type_never() {
        test_parse_type("!", Ty::Builtin(BuiltinType::Never).as_typ());
    }
}
