mod common;
mod pass1;

use crate::parser::AluminaVisitor;
use common::*;
use pass1::{FirstPassVisitor, Scope};
use std::cell::RefCell;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::rc::Rc;
use typed_arena::Arena;

const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");

pub mod parser {
    include!(concat!(env!("OUT_DIR"), "/parser.rs"));
}

#[derive(Debug, PartialEq, Eq)]
struct Field<'tcx> {
    name: String,
    ty: Ty<'tcx>,
}

struct Struct<'tcx> {
    fields: Vec<Field<'tcx>>,
}

#[derive(Debug, PartialEq, Copy, Clone, Eq, Hash)]
enum BuiltinType {
    Void,
    Never,
    U8,
    U16,
    U32,
    U64,
    U128,
    USize,
    ISize,
    I8,
    I16,
    I32,
    I64,
    I128,
    F32,
    F64,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
enum Ty<'tcx> {
    Placeholder(SymbolId<'tcx>),
    StructOrEnum(SymbolId<'tcx>),
    Builtin(BuiltinType),
    Pointer(TyP<'tcx>),
    Array(TyP<'tcx>, usize),
    Tuple(Vec<TyP<'tcx>>),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
struct TyP<'tcx> {
    inner: &'tcx Ty<'tcx>,
}

use std::borrow::Borrow;

impl<'tcx> Borrow<Ty<'tcx>> for TyP<'tcx> {
    fn borrow(&self) -> &'_ Ty<'tcx> {
        self.inner
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
struct SymbolId<'tcx> {
    id: usize,
    _phantom: PhantomData<&'tcx ()>,
}

struct GlobalCtx<'tcx> {
    arena: Arena<Ty<'tcx>>,
    types: RefCell<HashSet<TyP<'tcx>>>,
}

impl<'tcx> GlobalCtx<'tcx> {
    pub fn intern(&'tcx self, ty: Ty<'tcx>) -> TyP<'tcx> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return *key;
        }

        let id = self.arena.alloc(ty);
        let result = TyP { inner: id };
        self.types.borrow_mut().insert(result);
        result
    }
}

struct TypeVisitor<'tcx> {
    source: &'tcx str,
    global_ctx: &'tcx GlobalCtx<'tcx>,
    scope: Rc<RefCell<Scope<'tcx>>>,
}

impl<'tcx> AluminaVisitor<'tcx> for TypeVisitor<'tcx> {
    type ReturnType = Result<Ty<'tcx>, SyntaxError<'tcx>>;

    fn visit_primitive_type(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<Ty<'tcx>, SyntaxError<'tcx>> {
        match &self.source[node.byte_range()] {
            "void" => Ok(Ty::Builtin(BuiltinType::Void)),
            "u8" => Ok(Ty::Builtin(BuiltinType::U8)),
            "u16" => Ok(Ty::Builtin(BuiltinType::U16)),
            "u32" => Ok(Ty::Builtin(BuiltinType::U32)),
            "u64" => Ok(Ty::Builtin(BuiltinType::U64)),
            "u128" => Ok(Ty::Builtin(BuiltinType::U128)),
            "usize" => Ok(Ty::Builtin(BuiltinType::USize)),
            "isize" => Ok(Ty::Builtin(BuiltinType::ISize)),
            "i8" => Ok(Ty::Builtin(BuiltinType::I8)),
            "i16" => Ok(Ty::Builtin(BuiltinType::I16)),
            "i32" => Ok(Ty::Builtin(BuiltinType::I32)),
            "i64" => Ok(Ty::Builtin(BuiltinType::I64)),
            "i128" => Ok(Ty::Builtin(BuiltinType::I128)),
            "f32" => Ok(Ty::Builtin(BuiltinType::F32)),
            "f64" => Ok(Ty::Builtin(BuiltinType::F64)),
            _ => Err(SyntaxError("unknown type", node)),
        }
    }

    fn visit_never_type(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<Ty<'tcx>, SyntaxError<'tcx>> {
        Ok(Ty::Builtin(BuiltinType::Never))
    }

    fn visit_pointer_of(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<Ty<'tcx>, SyntaxError<'tcx>> {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(Ty::Pointer(self.global_ctx.intern(ty)))
    }

    fn visit_array_of(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<Ty<'tcx>, SyntaxError<'tcx>> {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let len = self.source[node.child_by_field_name("size").unwrap().byte_range()]
            .parse()
            .unwrap();

        Ok(Ty::Array(self.global_ctx.intern(ty), len))
    }

    fn visit_tuple_type(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<Ty<'tcx>, SyntaxError<'tcx>> {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field_name("element", &mut cursor)
            .map(|child| Ok(self.global_ctx.intern(self.visit(child)?)))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Ty::Tuple(elements))
    }
}

fn main() {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(parser::language()).unwrap();

    let parsed = parser.parse(SOURCE_CODE, None).unwrap();
    let root_node = parsed.root_node();

    let mut root_path: Path<'_> = PathSegment::Ident("hello_world").into();
    root_path.absolute = true;

    let mut visitor = FirstPassVisitor::new(SOURCE_CODE, root_path);
    visitor.visit(root_node).unwrap();

    println!("{:#?}", visitor.root_scope);
}

#[cfg(test)]
mod tests {
    use super::*;

    trait AsTyP {
        fn as_typ(&self) -> TyP<'_>;
    }

    impl AsTyP for Ty<'_> {
        fn as_typ(&self) -> TyP<'_> {
            TyP { inner: self }
        }
    }

    fn parse(src: &'static str) -> Rc<RefCell<Scope<'_>>> {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(parser::language()).unwrap();

        let parsed = Box::leak(Box::new(parser.parse(src, None).unwrap()));
        let root_node = parsed.root_node();

        let mut root_path: Path<'_> = PathSegment::Ident("hello_world").into();
        root_path.absolute = true;

        let mut visitor = FirstPassVisitor::new(src, root_path);
        visitor.visit(root_node).unwrap();

        visitor.root_scope
    }

    #[test]
    fn test_typ_eq() {
        let mut ctx = GlobalCtx {
            arena: Arena::new(),
            types: RefCell::new(HashSet::new()),
        };

        let ty1 = Ty::Builtin(BuiltinType::I32);
        let ty2 = Ty::Builtin(BuiltinType::I32);

        let ptr1 = Ty::Pointer(ctx.intern(ty1));
        let ptr2 = Ty::Pointer(ctx.intern(ty2));

        let typ1 = ctx.intern(ptr1);
        let typ2 = ctx.intern(ptr2);

        assert_eq!(typ1, typ2);
    }

    fn test_parse_type(typedef: &str, expected: Ty<'_>) {
        let global_ctx = GlobalCtx {
            arena: Arena::new(),
            types: RefCell::new(HashSet::new()),
        };

        let src = &format!("struct a {{ b: {} }}", typedef);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(parser::language()).unwrap();

        let parsed = parser.parse(src, None).unwrap();
        let root_node = parsed.root_node();

        let mut root_path: Path<'_> = PathSegment::Ident("hello_world").into();
        root_path.absolute = true;

        let mut visitor = FirstPassVisitor::new(src, root_path);
        visitor.visit(root_node).unwrap();

        let scope = &(*visitor.root_scope).borrow().children[0];
        let s = &(**scope).borrow().symbols["b"];

        let typ = match s {
            pass1::SymbolItem::Field(s) => s.child_by_field_name("type").unwrap(),
            _ => unreachable!(),
        };

        let mut visitor = TypeVisitor {
            source: src,
            global_ctx: &global_ctx,
            scope: scope.clone(),
        };

        let result = visitor.visit(typ).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_type_builtin() {
        test_parse_type("i32", Ty::Builtin(BuiltinType::I32));
    }

    #[test]
    fn test_parse_type_array() {
        test_parse_type(
            "[u32; 16]",
            Ty::Array(Ty::Builtin(BuiltinType::U32).as_typ(), 16),
        );
    }

    #[test]
    fn test_parse_type_pointer() {
        test_parse_type("&i32", Ty::Pointer(Ty::Builtin(BuiltinType::I32).as_typ()));
    }

    #[test]
    fn test_parse_type_tuple() {
        test_parse_type(
            "(i32, u32)",
            Ty::Tuple(vec![
                Ty::Builtin(BuiltinType::I32).as_typ(),
                Ty::Builtin(BuiltinType::U32).as_typ(),
            ]),
        );
    }

    #[test]
    fn test_parse_complex_tuple() {
        test_parse_type(
            "(i32, [u32; 16], &i32)",
            Ty::Tuple(vec![
                Ty::Builtin(BuiltinType::I32).as_typ(),
                Ty::Array(Ty::Builtin(BuiltinType::U32).as_typ(), 16).as_typ(),
                Ty::Pointer(Ty::Builtin(BuiltinType::I32).as_typ()).as_typ(),
            ]),
        );
    }

    #[test]
    fn test_parse_type_never() {
        test_parse_type("!", Ty::Builtin(BuiltinType::Never));
    }
}
