use std::fmt::Display;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

#[derive(PartialEq, Copy, Clone, Eq, Hash)]
pub struct NodeId {
    pub id: usize,
}

impl Display for NodeId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.id)
    }
}

impl Debug for NodeId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

use once_cell::unsync::OnceCell;

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
pub enum Ty<'gcx> {
    Placeholder(NodeId),
    Extern(NodeId),
    NamedType(SymbolP<'gcx>),
    Builtin(BuiltinType),
    Pointer(TyP<'gcx>),
    Array(TyP<'gcx>, usize),
    Slice(TyP<'gcx>),
    Tuple(&'gcx [TyP<'gcx>]),
    Function(&'gcx [TyP<'gcx>], TyP<'gcx>),
    GenericType(SymbolP<'gcx>, &'gcx [TyP<'gcx>]),
}

pub type TyP<'gcx> = &'gcx Ty<'gcx>;

#[derive(Debug)]
pub enum Symbol<'gcx> {
    Struct(Struct<'gcx>),
    Function(Function<'gcx>),
}

pub type SymbolP<'gcx> = &'gcx SymbolCell<'gcx>;

impl<'gcx> SymbolCell<'gcx> {
    pub fn assign(&self, value: Symbol<'gcx>) {
        // Panic if we try to assign the same symbol twice
        self.contents.set(value).unwrap();
    }

    pub fn get(&'gcx self) -> &'gcx Symbol<'gcx> {
        self.contents.get().unwrap()
    }
}

/// SymbolCell is a wrapper that allows us to build recursive structures incrementally.
/// This allows us to assign symbols to syntax early in name resolution and fill them in
/// later.
/// Symbols are immutable once they are assigned.
pub struct SymbolCell<'gcx> {
    pub id: NodeId,
    pub debug_name: Option<&'gcx str>,
    pub contents: OnceCell<Symbol<'gcx>>,
}

impl Hash for SymbolCell<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// Symbols have reference semantics. Two structs with the same fields
/// are not considered equal.
impl PartialEq for SymbolCell<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for SymbolCell<'_> {}

impl Debug for SymbolCell<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let debug_name = self.debug_name.unwrap_or("<unnamed>");

        if fmt.alternate() {
            writeln!(fmt, "{} ({}) {{", self.id, debug_name)?;
            writeln!(fmt, "\t{:?}", self.contents.get())?;
            writeln!(fmt, "}}")?;
        } else {
            write!(fmt, "{} ({})", self.id, debug_name)?
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Field<'gcx> {
    pub name: &'gcx str,
    pub ty: TyP<'gcx>,
}

#[derive(Debug)]
pub struct Struct<'gcx> {
    pub placeholders: &'gcx [NodeId],
    pub associated_fns: &'gcx [SymbolP<'gcx>],
    pub fields: &'gcx [Field<'gcx>],
}

#[derive(Debug, Clone, Copy)]
pub struct Parameter<'gcx> {
    pub id: NodeId,
    pub ty: TyP<'gcx>,
}

#[derive(Debug)]
pub struct Function<'gcx> {
    pub placeholders: &'gcx [NodeId],
    pub parameters: &'gcx [Parameter<'gcx>],
    pub return_type: TyP<'gcx>,
    pub body: Option<ExprP<'gcx>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct LetDeclaration<'gcx> {
    pub id: NodeId,
    pub typ: Option<TyP<'gcx>>,
    pub value: Option<ExprP<'gcx>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Statement<'gcx> {
    Expression(ExprP<'gcx>),
    LetDeclaration(LetDeclaration<'gcx>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum BinOp {
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Neq,
    Lt,
    LEq,
    Gt,
    GEq,
    LShift,
    Rsh,
    Plus,
    Minus,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Lit<'gcx> {
    Str(&'gcx str),
    Byte(u8),
    Int(u128),
    Float(&'gcx str),
    Bool(bool),
    Null,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Expr<'gcx> {
    Block(&'gcx [Statement<'gcx>], ExprP<'gcx>),
    Binary(ExprP<'gcx>, BinOp, ExprP<'gcx>),
    Call(ExprP<'gcx>, &'gcx [ExprP<'gcx>]),
    Function(SymbolP<'gcx>),
    Ref(ExprP<'gcx>),
    Deref(ExprP<'gcx>),
    Unary(UnOp, ExprP<'gcx>),
    Assign(ExprP<'gcx>, ExprP<'gcx>),
    AssignOp(BinOp, ExprP<'gcx>, ExprP<'gcx>),
    Local(NodeId),
    Lit(Lit<'gcx>),
    Tuple(&'gcx [ExprP<'gcx>]),
    Field(ExprP<'gcx>, &'gcx str),
    TupleIndex(ExprP<'gcx>, usize),
    If(ExprP<'gcx>, ExprP<'gcx>, ExprP<'gcx>),
    Cast(ExprP<'gcx>, TyP<'gcx>),

    // Generics support
    DeferredFunction(NodeId, &'gcx str),
    GenericFunction(ExprP<'gcx>, &'gcx [TyP<'gcx>]),

    Void,
}

pub type ExprP<'gcx> = &'gcx Expr<'gcx>;
