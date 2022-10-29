pub mod functions;
pub mod types;

use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    fmt::{Display, Write},
};

use crate::{
    ast::BuiltinType,
    common::{AluminaError, Incrementable},
    global_ctx::GlobalCtx,
    ir::{IRItem, IRItemP, Ty},
};
use bumpalo::Bump;

use crate::ir::{IrId, TyP};

macro_rules! w {
    ($buf:expr, $($arg:tt)*) => (
        ::std::write!($buf, $($arg)*).unwrap()
    );
}

pub(crate) use w;

use self::{functions::FunctionWriter, types::TypeWriter};

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum CName<'gen> {
    Native(&'gen str),
    Mangled(&'gen str, usize),
    Id(usize),
}

impl<'gen> CName<'gen> {
    pub fn from_native(name: &'gen str) -> Self {
        Self::Native(name)
    }

    fn mangle(self, id: usize) -> CName<'gen> {
        use CName::*;

        match self {
            Native(name) => Mangled(name, id),
            Mangled(name, _) => Mangled(name, id),
            Id(_) => Id(id),
        }
    }
}

pub struct CodegenCtx<'ir, 'gen> {
    global_ctx: GlobalCtx,
    id_map: RefCell<HashMap<IrId, CName<'gen>>>,
    type_map: RefCell<HashMap<TyP<'ir>, CName<'gen>>>,
    counter: Cell<usize>,
    arena: Bump,
}

impl<'ir, 'gen> CodegenCtx<'ir, 'gen> {
    pub fn new(global_ctx: GlobalCtx) -> Self {
        Self {
            global_ctx,
            arena: Bump::new(),
            id_map: RefCell::new(HashMap::new()),
            type_map: RefCell::new(HashMap::new()),
            counter: Cell::new(0),
        }
    }

    pub fn register_name(&self, id: IrId, name: CName<'gen>) {
        let mut map = self.id_map.borrow_mut();
        if map.insert(id, name).is_some() {
            panic!("name already registered, this is a bug");
        }
    }

    pub fn register_type(&self, typ: TyP<'ir>, name: CName<'gen>) {
        let mut map = self.type_map.borrow_mut();
        if map.insert(typ, name).is_some() {
            panic!("name already registered, this is a bug");
        }
    }

    pub fn get_name(&self, id: IrId) -> CName<'gen> {
        let mut map = self.id_map.borrow_mut();
        *map.entry(id)
            .or_insert_with(|| CName::Id(self.counter.increment()))
    }

    pub fn get_name_with_hint(&'gen self, name: &str, id: IrId) -> CName<'gen> {
        let mut map = self.id_map.borrow_mut();
        *map.entry(id)
            .or_insert_with(|| CName::Mangled(self.arena.alloc_str(name), self.counter.increment()))
    }

    pub fn get_type(&self, typ: TyP<'ir>) -> CName<'gen> {
        let map = self.type_map.borrow();
        *map.get(typ)
            .unwrap_or_else(|| panic!("type {:?} was not registered", typ))
    }

    pub fn get_type_maybe(&self, typ: TyP<'ir>) -> Option<CName<'gen>> {
        let map = self.type_map.borrow();
        map.get(typ).copied()
    }

    pub fn make_id(&self) -> usize {
        self.counter.increment()
    }
}

impl Display for CName<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CName::*;
        match self {
            Native(name) => f.write_str(name),
            Mangled(name, id) => {
                write!(f, "_AL{}{}{}", name.len(), name, id)
            }
            Id(id) => write!(f, "_AL0{}", id),
        }
    }
}

pub fn codegen(global_ctx: GlobalCtx, items: &[IRItemP<'_>]) -> Result<String, AluminaError> {
    let ctx = CodegenCtx::new(global_ctx);
    let type_writer = TypeWriter::new(&ctx);

    type_writer.add_type(&Ty::Builtin(BuiltinType::Void))?;

    let mut function_writer = FunctionWriter::new(&ctx, &type_writer);

    for item in items {
        match item.get().unwrap() {
            IRItem::Function(f) => function_writer.write_function_decl(item.id, f)?,
            IRItem::Static(t) => function_writer.write_static_decl(item.id, t)?,
            IRItem::Const(t) => function_writer.write_const_decl(item.id, t)?,
            _ => {}
        }
    }

    for item in items {
        match item.get().unwrap() {
            IRItem::Function(f) => function_writer.write_function_body(item.id, f)?,
            IRItem::Const(t) => function_writer.write_const(item.id, t)?,
            _ => {}
        }
    }

    let mut buf = String::with_capacity(512 * 1024);
    writeln!(buf, "#include <stdint.h>").unwrap();
    writeln!(buf, "#include <stddef.h>").unwrap();
    writeln!(
        buf,
        "#pragma clang diagnostic ignored \"-Wunknown-warning-option\""
    )
    .unwrap();
    writeln!(
        buf,
        "#pragma clang diagnostic ignored \"-Wparentheses-equality\""
    )
    .unwrap();
    writeln!(
        buf,
        "#pragma clang diagnostic ignored \"-Wincompatible-library-redeclaration\""
    )
    .unwrap();
    writeln!(buf, "#pragma clang diagnostic ignored \"-Wunused-value\"").unwrap();
    writeln!(
        buf,
        "#pragma GCC diagnostic ignored \"-Wbuiltin-declaration-mismatch\""
    )
    .unwrap();
    type_writer.write(&mut buf);
    function_writer.write(&mut buf);

    Ok(buf)
}
