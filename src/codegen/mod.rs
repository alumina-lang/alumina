use std::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap, HashSet},
    fmt::{Display, Write},
    marker::PhantomData,
    rc::Rc,
};

use crate::common::Incrementable;
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
    buffer: String,
    decl_map: HashMap<TyP<'ir>, Rc<OnceCell<CName>>>,
    body_map: HashSet<TyP<'ir>>,
    id_map: RefCell<HashMap<IrId, CName>>,
    counter: Cell<usize>,
    _phantom: PhantomData<&'cod ()>,
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

    fn pointer(self) -> CName {
        use CName::*;
        match self {
            Native(name) => Mangled(name, "p".to_string()),
            Mangled(name, mut suffix) => {
                suffix.push('p');
                Mangled(name, suffix)
            }
            Id(i) => Mangled(format!("al{}", i), "p".to_string()),
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
            buffer: String::with_capacity(100 * 1024),
            decl_map: HashMap::new(),
            body_map: HashSet::new(),
            id_map: RefCell::new(HashMap::new()),
            counter: Cell::new(0),
            _phantom: PhantomData,
        };

        result.write_prelude();
        result
    }

    fn write_prelude(&mut self) {
        writeln!(self.buffer, "#include <stdint.h>").unwrap();
    }

    fn get_ir_id(&self, id: IrId) -> CName {
        self.id_map
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| CName::Id(self.counter.increment()))
            .clone()
    }

    fn get_type_name(&mut self, ty: TyP<'ir>) -> Result<CName, AluminaError> {
        let cell = match self.decl_map.entry(ty) {
            Entry::Occupied(e) => {
                let cell = e.get();
                match cell.get() {
                    Some(n) => return Ok(n.clone()),
                    None => panic!(),
                }
            }
            Entry::Vacant(v) => {
                let item = Rc::new(OnceCell::new());
                v.insert(item).clone()
            }
        };

        let decl = match ty {
            Ty::Builtin(a) => {
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
                    BuiltinType::ISize => "ssize_t",
                    BuiltinType::Bool => "bool",
                    BuiltinType::Void => "void",
                    _ => todo!(),
                });

                cell.set(name.clone()).unwrap();
                name
            }
            Ty::Pointer(a, is_const) => {
                let inner = self.get_type_name(a)?;
                let name = inner.clone().pointer();

                if *is_const {
                    writeln!(self.buffer, "typedef const {} *{};", inner, name).unwrap();
                } else {
                    writeln!(self.buffer, "typedef {} *{};", inner, name).unwrap();
                }

                cell.set(name.clone()).unwrap();
                name
            }
            Ty::Array(a, len) => {
                let inner = self.get_type_name(a)?;
                let name = inner.array(*len);

                writeln!(self.buffer, "typedef struct {0} {0};", name).unwrap();
                cell.set(name.clone()).unwrap();

                name
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    let name = CName::Id(self.counter.increment());

                    writeln!(self.buffer, "typedef struct {0} {0};", name).unwrap();
                    cell.set(name.clone()).unwrap();

                    name
                }
                _ => todo!(),
            },
            _ => todo!(),
        };

        Ok(decl)
    }

    fn write_body(&mut self, ty: TyP<'ir>) -> Result<(), AluminaError> {
        if self.body_map.contains(&ty) {
            return Ok(());
        }

        match ty {
            Ty::Array(a, len) => {
                let name = self.get_type_name(ty)?;
                let inner = self.get_type_name(a)?;

                self.write_body(a)?;

                writeln!(self.buffer, "struct {} {{", name).unwrap();
                writeln!(self.buffer, "  {} __data[{}];", inner, len).unwrap();
                writeln!(self.buffer, "}};").unwrap();
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    let name = self.get_type_name(ty)?;

                    let mut buf = String::with_capacity(256);
                    writeln!(buf, "struct {} {{", name).unwrap();
                    for f in s.fields {
                        self.write_body(f.ty)?;

                        writeln!(
                            buf,
                            "  {} {};",
                            self.get_type_name(f.ty)?,
                            self.get_ir_id(f.id)
                        )
                        .unwrap();
                    }
                    writeln!(buf, "}};").unwrap();

                    self.buffer.push_str(&buf);
                }
                _ => todo!(),
            },
            _ => (),
        };

        self.body_map.insert(ty);

        Ok(())
    }

    pub fn write_item(&mut self, item: IRItemP<'ir>) -> Result<(), AluminaError> {
        match item.get() {
            IRItem::Function(ty) => {
                self.get_type_name(ty.return_type)?;
                for arg in ty.args.iter() {
                    self.get_type_name(arg.ty)?;
                }
            }
            IRItem::Enum(ty) => {
                self.get_type_name(ty.underlying_type)?;
            }
            _ => {}
        }

        Ok(())
    }

    pub fn generate(mut self) -> String {
        let all_types = self.decl_map.keys().cloned().collect::<Vec<_>>();
        for ty in all_types {
            self.write_body(ty).unwrap();
        }

        self.buffer
    }
}
