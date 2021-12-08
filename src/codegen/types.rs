use std::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    fmt::{Display, Write},
    marker::PhantomData,
    rc::Rc,
};

use crate::{
    ast::{BinOp, UnOp, Attribute, AttributeKind},
    common::Incrementable,
    ir::{ExprKind, ExprP, Function, Statement},
};
use once_cell::unsync::OnceCell;

use crate::{
    ast::BuiltinType,
    common::AluminaError,
    ir::{IRItem, IRItemP, IrId, Struct, Ty, TyP},
};

#[derive(Debug)]
struct Decl {
    name: String,
}

pub struct CCodegen<'ir, 'cod> {
    type_decls: String,
    type_bodies: String,

    indent: usize,

    decl_map: HashMap<TyP<'ir>, Rc<OnceCell<CName>>>,
    body_map: HashSet<TyP<'ir>>,
    needs_body: HashSet<TyP<'ir>>,
    id_map: RefCell<HashMap<IrId, CName>>,
    counter: Cell<usize>,
    _phantom: PhantomData<&'cod ()>,
}

macro_rules! w {
    ($buf:expr, $($arg:tt)*) => (
        write!($buf, $($arg)*).unwrap()
    );
}

#[derive(Clone, Debug)]
pub enum CName {
    Native(String),
    Id(usize),
    Mangled(String, String),
}

impl CName {
    pub fn from_native(name: &str) -> Self {
        Self::Native(name.to_string())
    }

    fn pointer(self, is_const: bool) -> CName {
        use CName::*;
        let suf = if is_const { "cp" } else { "p" };

        match self {
            Native(name) => Mangled(name, suf.to_string()),
            Mangled(name, mut suffix) => {
                suffix.push_str(suf);
                Mangled(name, suffix)
            }
            Id(i) => Mangled(format!("al{}", i), suf.to_string()),
        }
    }

    fn array(self, size: usize) -> CName {
        use CName::*;
        match self {
            Native(name) => Mangled(name, format!("A{}", size)),
            Mangled(name, mut suffix) => {
                write!(&mut suffix, "A{}", size).unwrap();
                Mangled(name, suffix)
            }
            Id(i) => Mangled(format!("al{}", i), format!("A{}", size)),
        }
    }
}

impl Display for CName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CName::*;
        match self {
            Native(name) => write!(f, "{}", name),
            Mangled(name, suffix) => {
                write!(
                    f,
                    "{}_{}",
                    name.replace("_", "__"),
                    suffix.replace("_", "__")
                )
            }
            Id(i) => write!(f, "al{}", i),
        }
    }
}

impl<'ir, 'cod> CCodegen<'ir, 'cod> {
    pub fn new() -> Self {
        let mut result = Self {
            type_decls: String::with_capacity(10 * 1024),
            type_bodies: String::with_capacity(10 * 1024),
            fn_decls: String::with_capacity(10 * 1024),
            fn_bodies: String::with_capacity(10 * 1024),
            indent: 0,
            decl_map: HashMap::new(),
            body_map: HashSet::new(),
            needs_body: HashSet::new(),
            id_map: RefCell::new(HashMap::new()),
            counter: Cell::new(0),
            _phantom: PhantomData,
        };

        result.write_prelude();
        result
    }

    fn write_prelude(&mut self) {
        writeln!(self.type_decls, "#include <stdint.h>").unwrap();
        writeln!(self.type_decls, "#include <stddef.h>").unwrap();
    }

    fn ir_name(&self, id: IrId, provided_name: Option<&'ir str>) -> CName {
        self.id_map
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| {
                provided_name
                    .map(|name| CName::Native(name.to_string()))
                    .unwrap_or(CName::Id(self.counter.increment()))
            })
            .clone()
    }

    fn ty_name(&self, ty: TyP<'ir>) -> CName {
        self.decl_map.get(ty).unwrap().get().unwrap().clone()
    }

    fn ensure_ty(&mut self, ty: TyP<'ir>, ref_only: bool) -> Result<(), AluminaError> {
        if let Ty::Fn(_, _) = ty {
            return Ok(());
        }

        let (cell, body_only) = match self.decl_map.entry(ty) {
            Entry::Occupied(e) => {
                let cell = e.get();
                match cell.get() {
                    Some(n) => {
                        if !ref_only && !self.needs_body.contains(ty) {
                            (cell.clone(), true)
                        } else {
                            return Ok(());
                        }
                    }
                    None => return Err(AluminaError::CycleDetected),
                }
            }
            Entry::Vacant(v) => {
                let item = Rc::new(OnceCell::new());
                (v.insert(item).clone(), false)
            }
        };

        match ty {
            Ty::Builtin(a) if !body_only => {
                let name = CName::from_native(match a {
                    BuiltinType::U8 => "uint8_t",
                    BuiltinType::U16 => "uint16_t",
                    BuiltinType::U32 => "uint32_t",
                    BuiltinType::U64 => "uint64_t",
                    BuiltinType::I8 => "int8_t",
                    BuiltinType::I16 => "int16_t",
                    BuiltinType::I32 => "int32_t",
                    BuiltinType::I64 => "int64_t",
                    BuiltinType::F32 => "float",
                    BuiltinType::F64 => "double",
                    BuiltinType::USize => "size_t",
                    BuiltinType::ISize => "ptrdiff_t",
                    BuiltinType::Bool => "_Bool",
                    BuiltinType::Void => "void",
                    BuiltinType::Never => "void",
                    _ => todo!(),
                });

                cell.set(name).unwrap();
            }
            Ty::Pointer(inner, is_const) if !body_only => {
                self.ensure_ty(inner, true)?;

                let inner = self.ty_name(inner);
                let name = inner.clone().pointer(*is_const);

                if *is_const {
                    w!(self.type_decls, "typedef const {} *{};\n", inner, name);
                } else {
                    w!(self.type_decls, "typedef {} *{};\n", inner, name);
                }

                cell.set(name).unwrap();
            }
            Ty::Array(inner, len) if !body_only => {
                self.ensure_ty(inner, false)?;
                let name = self.ty_name(inner).array(*len);

                w!(self.type_decls, "typedef struct {0} {0};\n", name);
                cell.set(name).unwrap();

                self.needs_body.insert(ty);
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    if !body_only {
                        let name = CName::Id(self.counter.increment());
                        w!(self.type_decls, "typedef struct {0} {0};\n", name);
                        cell.set(name).unwrap();
                    }

                    if !ref_only {
                        self.needs_body.insert(ty);
                        for field in s.fields {
                            self.ensure_ty(field.ty, false)?;
                        }
                    }
                }
                _ => {}
            },
            Ty::Tuple(items) if !body_only => {
                for elem in items.iter() {
                    self.ensure_ty(elem, false)?;
                }

                let name = CName::Id(self.counter.increment());
                w!(self.type_decls, "typedef struct {0} {0};\n", name);

                cell.set(name).unwrap();
                self.needs_body.insert(ty);
            }
            _ => {}
        };

        Ok(())
    }

    fn write_type_body(&mut self, ty: TyP<'ir>) -> Result<(), AluminaError> {
        if self.body_map.contains(&ty) {
            return Ok(());
        }

        match ty {
            Ty::Array(a, len) => {
                let name = self.ty_name(ty);
                let inner = self.ty_name(a);

                self.write_type_body(a)?;

                w!(self.type_bodies, "struct {} {{\n", name);
                w!(self.type_bodies, "  {} __data[{}];\n", inner, len);
                w!(self.type_bodies, "}};\n");
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    let name = self.ty_name(ty);

                    for f in s.fields {
                        self.write_type_body(f.ty)?;
                    }

                    w!(self.type_bodies, "struct {} {{\n", name);
                    for f in s.fields {
                        w!(
                            self.type_bodies,
                            "  {} {};\n",
                            self.ty_name(f.ty),
                            self.ir_name(f.id, None)
                        );
                    }
                    w!(self.type_bodies, "}};\n");
                }
                _ => todo!(),
            },
            Ty::Tuple(items) => {
                let name = self.ty_name(ty);

                for f in items.iter() {
                    self.write_type_body(f)?;
                }

                w!(self.type_bodies, "struct {} {{\n", name);
                for (idx, f) in items.iter().enumerate() {
                    w!(self.type_bodies, "  {} _{};\n", self.ty_name(f), idx);
                }
                w!(self.type_bodies, "}};\n");
            }
            _ => (),
        };

        self.body_map.insert(ty);

        Ok(())
    }

    pub fn generate(mut self) -> String {
        let needs_body = self.needs_body.clone();
        for ty in needs_body {
            self.write_type_body(ty).unwrap();
        }

        let mut buf = String::with_capacity(
            self.type_decls.len()
                + self.type_bodies.len()
                + self.fn_decls.len()
                + self.fn_bodies.len(),
        );

        buf.push_str(&self.type_decls);
        buf.push_str(&self.type_bodies);
        buf.push_str(&self.fn_decls);
        buf.push_str(&self.fn_bodies);

        buf
    }
}
