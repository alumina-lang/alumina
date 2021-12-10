use std::{cell::RefCell, collections::HashSet, fmt::Write};

use crate::{
    ast::BuiltinType,
    codegen::w,
    common::AluminaErrorKind,
    ir::{IRItem, Ty, TyP},
};

use super::{CName, CodegenCtx};

#[derive(Debug)]
struct Decl {
    name: String,
}

struct TypeWriterInner<'ir, 'gen> {
    ctx: &'gen CodegenCtx<'ir, 'gen>,

    type_decls: String,
    type_bodies: String,

    body_map: HashSet<TyP<'ir>>,
    needs_body: HashSet<TyP<'ir>>,
}

pub struct TypeWriter<'ir, 'gen> {
    ctx: &'gen CodegenCtx<'ir, 'gen>,
    inner: RefCell<TypeWriterInner<'ir, 'gen>>,
}

impl<'ir, 'gen> TypeWriter<'ir, 'gen> {
    pub fn new(ctx: &'gen CodegenCtx<'ir, 'gen>) -> Self {
        Self {
            ctx,
            inner: RefCell::new(TypeWriterInner {
                ctx,
                type_decls: String::with_capacity(10 * 1024),
                type_bodies: String::with_capacity(10 * 1024),
                body_map: HashSet::new(),
                needs_body: HashSet::new(),
            }),
        }
    }

    pub fn add_type(&self, ty: TyP<'ir>) -> Result<(), AluminaErrorKind> {
        self.inner.borrow_mut().add_type(ty, false)
    }

    pub fn write(&self, buf: &mut String) {
        let mut inner = self.inner.borrow_mut();

        let needs_body = inner.needs_body.clone();
        for ty in needs_body {
            inner.write_type_body(ty).unwrap();
        }

        buf.push_str(&inner.type_decls);
        buf.push_str(&inner.type_bodies);
    }
}

impl<'ir, 'gen> TypeWriterInner<'ir, 'gen> {
    fn add_type(&mut self, ty: TyP<'ir>, ref_only: bool) -> Result<(), AluminaErrorKind> {
        let body_only = match self.ctx.get_type_maybe(ty) {
            Some(_) if ref_only || self.needs_body.contains(ty) => return Ok(()),
            Some(_) => true,
            None => false,
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

                self.ctx.register_type(ty, name);
            }
            Ty::Pointer(inner, is_const) if !body_only => {
                self.add_type(inner, true)?;

                let inner = self.ctx.get_type(inner);
                let name = inner.mangle(self.ctx.make_id());

                if *is_const {
                    w!(self.type_decls, "typedef const {} *{};\n", inner, name);
                } else {
                    w!(self.type_decls, "typedef {} *{};\n", inner, name);
                }

                self.ctx.register_type(ty, name);
            }
            Ty::Array(inner, _len) if !body_only => {
                self.add_type(inner, false)?;
                let name = self.ctx.get_type(inner).mangle(self.ctx.make_id());

                w!(self.type_decls, "typedef struct {0} {0};\n", name);
                self.ctx.register_type(ty, name);

                self.needs_body.insert(ty);
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    if !body_only {
                        let name = if let Some(name) = s.name {
                            self.ctx.get_name_with_hint(name, item.id)
                        } else {
                            self.ctx.get_name(item.id)
                        };

                        w!(self.type_decls, "typedef struct {0} {0};\n", name);
                        self.ctx.register_type(ty, name);
                    }

                    if !ref_only {
                        self.needs_body.insert(ty);
                        for f in s.fields {
                            self.add_type(f.ty, false)?;
                        }
                    }
                }
                IRItem::Enum(s) if !body_only => {
                    self.add_type(s.underlying_type, false)?;
                    self.ctx
                        .register_type(ty, self.ctx.get_type(s.underlying_type));
                }
                _ => {}
            },
            Ty::Tuple(items) if !body_only => {
                for elem in items.iter() {
                    self.add_type(elem, false)?;
                }

                let name = CName::Id(self.ctx.make_id());
                w!(self.type_decls, "typedef struct {0} {0};\n", name);

                self.ctx.register_type(ty, name);
                self.needs_body.insert(ty);
            }
            Ty::Fn(args, ret) if !body_only => {
                for elem in args.iter() {
                    self.add_type(elem, false)?;
                }
                self.add_type(ret, false)?;

                let name = CName::Id(self.ctx.make_id());
                self.ctx.register_type(ty, name);

                w!(
                    self.type_decls,
                    "typedef {0} (*{1})(",
                    self.ctx.get_type(ret),
                    name
                );
                for (i, elem) in args.iter().enumerate() {
                    if i > 0 {
                        w!(self.type_decls, ", ");
                    }
                    w!(self.type_decls, "{0}", self.ctx.get_type(elem));
                }
                w!(self.type_decls, ");\n");
            }
            _ => {}
        };

        Ok(())
    }

    fn write_type_body(&mut self, ty: TyP<'ir>) -> Result<(), AluminaErrorKind> {
        if self.body_map.contains(&ty) {
            return Ok(());
        }

        match ty {
            Ty::Array(a, len) => {
                let name = self.ctx.get_type(ty);
                let inner = self.ctx.get_type(a);

                self.write_type_body(a)?;

                w!(self.type_bodies, "struct {} {{\n", name);
                w!(self.type_bodies, "  {} __data[{}];\n", inner, len);
                w!(self.type_bodies, "}};\n");
            }
            Ty::NamedType(item) => match item.get() {
                IRItem::Struct(s) => {
                    let name = self.ctx.get_type(ty);

                    for f in s.fields {
                        self.write_type_body(f.ty)?;
                    }

                    w!(self.type_bodies, "struct {} {{\n", name);
                    for f in s.fields {
                        w!(
                            self.type_bodies,
                            "  {} {};\n",
                            self.ctx.get_type(f.ty),
                            self.ctx.get_name(f.id)
                        );
                    }
                    w!(self.type_bodies, "}};\n");
                }
                _ => todo!(),
            },
            Ty::Tuple(items) => {
                let name = self.ctx.get_type(ty);

                for f in items.iter() {
                    self.write_type_body(f)?;
                }

                w!(self.type_bodies, "struct {} {{\n", name);
                for (idx, f) in items.iter().enumerate() {
                    w!(self.type_bodies, "  {} _{};\n", self.ctx.get_type(f), idx);
                }
                w!(self.type_bodies, "}};\n");
            }
            _ => (),
        };

        self.body_map.insert(ty);

        Ok(())
    }
}
