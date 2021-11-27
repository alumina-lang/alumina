mod common;
mod pass1;
mod utils;

use crate::parser::AluminaVisitor;
use crate::pass1::ScopeType;
use bumpalo::Bump;
use common::*;
use pass1::{FirstPassVisitor, Scope, Item};
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;

// const SOURCE_CODE: &str = include_str!("../examples/minimal.alumina");
const SOURCE_CODE: &str = include_str!("../examples/vector.alumina");

pub mod parser {
    include!(concat!(env!("OUT_DIR"), "/parser.rs"));
}

#[derive(Debug, PartialEq, Eq)]
struct Field<'tcx> {
    name: String,
    ty: Ty<'tcx>,
}

trait Incrementable<T> {
    fn increment(&self) -> T;
}

impl Incrementable<usize> for Cell<usize> {
    fn increment(&self) -> usize {
        let old = self.get();
        self.set(old + 1);
        old
    }
}

struct Struct<'tcx> {
    fields: Vec<Field<'tcx>>,
}

#[derive(Debug, PartialEq, Copy, Clone, Eq, Hash)]
pub enum BuiltinType {
    Void,
    Never,
    Bool,
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
pub enum Ty<'tcx> {
    Placeholder(SymbolP<'tcx>),
    StructOrEnum(SymbolP<'tcx>),
    Builtin(BuiltinType),
    Pointer(TyP<'tcx>),
    Array(TyP<'tcx>, usize),
    Slice(TyP<'tcx>),
    Tuple(&'tcx [TyP<'tcx>]),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct TyP<'tcx> {
    inner: &'tcx Ty<'tcx>,
}

use std::borrow::Borrow;

impl<'tcx> Borrow<Ty<'tcx>> for TyP<'tcx> {
    fn borrow(&self) -> &'_ Ty<'tcx> {
        self.inner
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct SymbolP<'tcx> {
    id: usize,
    _phantom: PhantomData<&'tcx ()>,
}

impl Debug for SymbolP<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "SymbolP({})", self.id)
    }
}

pub struct GlobalCtx<'tcx> {
    arena: Bump,
    counter: Cell<usize>,
    types: RefCell<HashSet<TyP<'tcx>>>,
}

impl<'tcx> GlobalCtx<'tcx> {
    fn new() -> Self {
        Self {
            arena: Bump::new(),
            counter: Cell::new(0),
            types: RefCell::new(HashSet::new()),
        }
    }

    pub fn intern(&'tcx self, ty: Ty<'tcx>) -> TyP<'tcx> {
        if let Some(key) = self.types.borrow().get(&ty) {
            return *key;
        }

        let id = self.arena.alloc(ty);
        let result = TyP { inner: id };
        self.types.borrow_mut().insert(result);
        result
    }

    pub fn make_symbol(&'tcx self) -> SymbolP<'tcx> {
        SymbolP {
            id: self.counter.increment(),
            _phantom: PhantomData,
        }
    }
}

struct ScopedPathVisitor<'tcx> {
    source: &'tcx str,
    // global_ctx: &'tcx GlobalCtx<'tcx>
}

impl<'tcx> AluminaVisitor<'tcx> for ScopedPathVisitor<'tcx> {
    type ReturnType = Result<Path<'tcx>, SyntaxError<'tcx>>;

    fn visit_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let name = &self.source[node.byte_range()];

        Ok(PathSegment(name).into())
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let subpath = self.visit(node.child_by_field_name("path").unwrap())?;
        let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];

        Ok(subpath.extend(PathSegment(name)))
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let subpath = self.visit(node.child_by_field_name("path").unwrap())?;
        let name = &self.source[node.child_by_field_name("name").unwrap().byte_range()];

        Ok(subpath.extend(PathSegment(name)))
    }
}

struct TypeVisitor<'tcx> {
    source: &'tcx str,
    global_ctx: &'tcx GlobalCtx<'tcx>,
    scope: Scope<'tcx>,
}

impl<'tcx> TypeVisitor<'tcx> {
    fn visit_typeref(
        &mut self,
        node: tree_sitter::Node<'tcx>,
    ) -> Result<TyP<'tcx>, SyntaxError<'tcx>> {
        let mut visitor = ScopedPathVisitor {
            source: self.source,
            //global_ctx: self.global_ctx,
        };
        let path = visitor.visit(node)?;

        println!("HEYA! {:?}", path);

        Ok(self.global_ctx.intern(Ty::Builtin(BuiltinType::Void)))
    }
}

impl<'tcx> AluminaVisitor<'tcx> for TypeVisitor<'tcx> {
    type ReturnType = Result<TyP<'tcx>, SyntaxError<'tcx>>;

    fn visit_primitive_type(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let builtin = match &self.source[node.byte_range()] {
            "void" => Ty::Builtin(BuiltinType::Void),
            "bool" => Ty::Builtin(BuiltinType::Bool),
            "u8" => Ty::Builtin(BuiltinType::U8),
            "u16" => Ty::Builtin(BuiltinType::U16),
            "u32" => Ty::Builtin(BuiltinType::U32),
            "u64" => Ty::Builtin(BuiltinType::U64),
            "u128" => Ty::Builtin(BuiltinType::U128),
            "usize" => Ty::Builtin(BuiltinType::USize),
            "isize" => Ty::Builtin(BuiltinType::ISize),
            "i8" => Ty::Builtin(BuiltinType::I8),
            "i16" => Ty::Builtin(BuiltinType::I16),
            "i32" => Ty::Builtin(BuiltinType::I32),
            "i64" => Ty::Builtin(BuiltinType::I64),
            "i128" => Ty::Builtin(BuiltinType::I128),
            "f32" => Ty::Builtin(BuiltinType::F32),
            "f64" => Ty::Builtin(BuiltinType::F64),
            _ => return Err(SyntaxError("unknown type", node)),
        };

        Ok(self.global_ctx.intern(builtin))
    }

    fn visit_never_type(&mut self, _node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        Ok(self.global_ctx.intern(Ty::Builtin(BuiltinType::Never)))
    }

    fn visit_pointer_of(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;

        Ok(self.global_ctx.intern(Ty::Pointer(ty)))
    }

    fn visit_array_of(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        let len = self.source[node.child_by_field_name("size").unwrap().byte_range()]
            .parse()
            .unwrap();

        Ok(self.global_ctx.intern(Ty::Array(ty, len)))
    }

    fn visit_slice_of(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let ty = self.visit(node.child_by_field_name("inner").unwrap())?;
        Ok(self.global_ctx.intern(Ty::Slice(ty)))
    }

    fn visit_tuple_type(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let elements = node
            .children_by_field_name("element", &mut cursor)
            .map(|child| Ok(self.visit(child)?))
            .collect::<Result<Vec<_>, _>>()?;

        let slice = self.global_ctx.arena.alloc_slice_copy(elements.as_slice());

        Ok(self.global_ctx.intern(Ty::Tuple(slice)))
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        self.visit_typeref(node)
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'tcx>) -> Self::ReturnType {
        self.visit_typeref(node)
    }
}

fn main() {
    let global_ctx = GlobalCtx::new();
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(parser::language()).unwrap();

    let parsed = parser.parse(SOURCE_CODE, None).unwrap();
    let root_node = parsed.root_node();
    println!("{:#?}", utils::NodeWrapper::new(SOURCE_CODE, root_node));

    let root_scope = Scope::new();
    let module_scope = root_scope.make_child(ScopeType::Module, "main");
    root_scope
        .add_item("main", Item::Module(module_scope.clone()))
        .unwrap();

    let mut visitor = FirstPassVisitor::new(&global_ctx, SOURCE_CODE, module_scope);
    visitor.visit(root_node).unwrap();

    println!("{:#?}", root_scope);
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

    fn parse<'tcx>(global_ctx: &'tcx GlobalCtx<'tcx>, src: &'tcx str) -> Scope<'tcx> {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(parser::language()).unwrap();

        let parsed = global_ctx.arena.alloc(parser.parse(src, None).unwrap());
        let root_node = parsed.root_node();

        let root_scope = Scope::new();
        let module_scope = root_scope.make_child(ScopeType::Module, "test");
        root_scope
            .add_item("test", Item::Module(module_scope.clone()))
            .unwrap();

        let mut visitor = FirstPassVisitor::new(global_ctx, src, module_scope);
        visitor.visit(root_node).unwrap();

        root_scope
    }

    fn parse_type<'tcx>(global_ctx: &'tcx GlobalCtx<'tcx>, typedef: &'_ str) -> TyP<'tcx> {
        let src = global_ctx
            .arena
            .alloc_str(&format!("struct a {{ b: {}; }}", typedef));

        let root_scope = parse(global_ctx, src);
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

        let mut visitor = TypeVisitor {
            source: src,
            global_ctx,
            scope,
        };

        visitor.visit(node).unwrap()
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

        let result = parse_type(&global_ctx, typedef);

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
    fn test_parse_generic() {
        test_parse_type(
            "std::ptr<std::vec>",
            Ty::Tuple(&[
                Ty::Builtin(BuiltinType::I32).as_typ(),
                Ty::Builtin(BuiltinType::U32).as_typ(),
            ])
            .as_typ(),
        );
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
    fn test_referenced_type() {
        let global_ctx = GlobalCtx::new();

        let _result = parse_type(&global_ctx, "std::collections::ptr");
    }

    #[test]
    fn test_parse_type_never() {
        test_parse_type("!", Ty::Builtin(BuiltinType::Never).as_typ());
    }
}
