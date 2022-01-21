use std::{cell::RefCell, collections::HashSet, fmt::Write};

use crate::{
    ast::{Attribute, BuiltinType},
    codegen::w,
    common::AluminaError,
    ir::{IRItem, Ty, TyP},
};

use super::{CName, CodegenCtx};

struct TypeWriterInner<'ir, 'gen> {
    ctx: &'gen CodegenCtx<'ir, 'gen>,

    type_decls: String,
    type_bodies: String,

    body_map: HashSet<TyP<'ir>>,
    needs_body: HashSet<TyP<'ir>>,
}

pub struct TypeWriter<'ir, 'gen> {
    inner: RefCell<TypeWriterInner<'ir, 'gen>>,
}

impl<'ir, 'gen> TypeWriter<'ir, 'gen> {
    pub fn new(ctx: &'gen CodegenCtx<'ir, 'gen>) -> Self {
        Self {
            inner: RefCell::new(TypeWriterInner {
                ctx,
                type_decls: String::with_capacity(10 * 1024),
                type_bodies: String::with_capacity(10 * 1024),
                body_map: HashSet::new(),
                needs_body: HashSet::new(),
            }),
        }
    }

    pub fn add_type(&self, ty: TyP<'ir>) -> Result<(), AluminaError> {
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
    fn add_type(&mut self, ty: TyP<'ir>, ref_only: bool) -> Result<(), AluminaError> {
        let body_only = match self.ctx.get_type_maybe(ty) {
            Some(_) if ref_only || self.needs_body.contains(ty) => return Ok(()),
            Some(_) => true,
            None => false,
        };

        match ty {
            Ty::Builtin(a) if !body_only => {
                let name = match a {
                    BuiltinType::U128 => {
                        let name = CName::Mangled("uint128", self.ctx.make_id());
                        w!(self.type_decls, "typedef unsigned __int128 {};\n", name);
                        name
                    }
                    BuiltinType::I128 => {
                        let name = CName::Mangled("int128", self.ctx.make_id());
                        w!(self.type_decls, "typedef signed __int128 {};\n", name);
                        name
                    }
                    _ => CName::from_native(match a {
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
                        _ => unreachable!(),
                    }),
                };

                self.ctx.register_type(ty, name);
            }
            Ty::Pointer(inner, is_const) if !body_only => {
                self.add_type(inner, true)?;

                let inner = self.ctx.get_type(inner);
                let name = inner.mangle(self.ctx.make_id());

                assert!(inner != name);

                if *is_const {
                    w!(self.type_decls, "typedef const {} *{};\n", inner, name);
                } else {
                    w!(self.type_decls, "typedef {} *{};\n", inner, name);
                }

                self.ctx.register_type(ty, name);
            }
            Ty::Array(inner, _len) if !body_only => {
                assert!(!inner.is_zero_sized());

                self.add_type(inner, false)?;
                let name = self.ctx.get_type(inner).mangle(self.ctx.make_id());

                w!(self.type_decls, "typedef struct {0} {0};\n", name);
                self.ctx.register_type(ty, name);

                self.needs_body.insert(ty);
            }
            Ty::NamedType(item) => match item.get().unwrap() {
                IRItem::StructLike(s) => {
                    if !body_only {
                        let name = if let Some(name) = s.name {
                            self.ctx.get_name_with_hint(name, item.id)
                        } else {
                            self.ctx.get_name(item.id)
                        };

                        if s.is_union {
                            w!(self.type_decls, "typedef union {0} {0};\n", name);
                        } else {
                            w!(self.type_decls, "typedef struct {0} {0};\n", name);
                        }

                        self.ctx.register_type(ty, name);
                    }

                    if !ref_only {
                        self.needs_body.insert(ty);
                        for f in s.fields.iter().filter(|f| !f.ty.is_zero_sized()) {
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
                for elem in items.iter().filter(|f| !f.is_zero_sized()) {
                    self.add_type(elem, false)?;
                }

                let name = CName::Id(self.ctx.make_id());
                w!(self.type_decls, "typedef struct {0} {0};\n", name);

                self.ctx.register_type(ty, name);
                self.needs_body.insert(ty);
            }
            Ty::FunctionPointer(args, ret) if !body_only => {
                for elem in args.iter().filter(|f| !f.is_zero_sized()) {
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
                for (i, elem) in args.iter().filter(|f| !f.is_zero_sized()).enumerate() {
                    if i > 0 {
                        w!(self.type_decls, ", ");
                    }
                    w!(self.type_decls, "{0}", self.ctx.get_type(elem));
                }
                w!(self.type_decls, ");\n");
            }
            Ty::Unqualified(_) if !body_only => {
                // FIXME: unqualified string should not be given explicit types in
                // codegen.
                self.ctx.register_type(ty, CName::Id(self.ctx.make_id()));
            }
            _ => {}
        };

        Ok(())
    }

    fn write_type_body(&mut self, ty: TyP<'ir>) -> Result<(), AluminaError> {
        if !self.needs_body.contains(&ty) {
            return Ok(());
        }
        if self.body_map.contains(&ty) {
            return Ok(());
        }

        match ty {
            Ty::Array(inner, len) => {
                assert!(!inner.is_zero_sized());

                let name = self.ctx.get_type(ty);
                let inner_name = self.ctx.get_type(inner);

                self.write_type_body(inner)?;

                w!(self.type_bodies, "struct {} {{\n", name);
                w!(self.type_bodies, "  {} __data[{}];\n", inner_name, len);
                w!(self.type_bodies, "}};\n");
            }
            Ty::NamedType(item) => match item.get().unwrap() {
                IRItem::StructLike(s) => {
                    let name = self.ctx.get_type(ty);

                    for f in s.fields.iter().filter(|f| !f.ty.is_zero_sized()) {
                        self.write_type_body(f.ty)?;
                    }

                    let mut align = 0;
                    for attr in s.attributes {
                        if let Attribute::Align(val) = attr {
                            align = *val;
                            break;
                        }
                    }

                    if align > 0 {
                        // C11 _Alignas does not work on the entire struct, use an extension
                        // attribute instead.
                        if s.is_union {
                            w!(
                                self.type_bodies,
                                "union __attribute__((aligned ({}))) {} {{\n",
                                align,
                                name
                            );
                        } else {
                            w!(
                                self.type_bodies,
                                "struct __attribute__((aligned ({}))) {} {{\n",
                                align,
                                name
                            );
                        }
                    } else {
                        if s.is_union {
                            w!(self.type_bodies, "union {} {{\n", name);
                        } else {
                            w!(self.type_bodies, "struct {} {{\n", name);
                        }
                    }

                    for f in s.fields.iter().filter(|f| !f.ty.is_zero_sized()) {
                        w!(
                            self.type_bodies,
                            "  {} {};\n",
                            self.ctx.get_type(f.ty),
                            self.ctx.get_name(f.id)
                        );
                    }
                    w!(self.type_bodies, "}};\n");
                }
                _ => panic!("unimplemented: {:?}", ty),
            },
            Ty::Tuple(items) => {
                let name = self.ctx.get_type(ty);

                for f in items.iter().filter(|f| !f.is_zero_sized()) {
                    self.write_type_body(f)?;
                }

                w!(self.type_bodies, "struct {} {{\n", name);
                for (idx, f) in items.iter().enumerate().filter(|(_, f)| !f.is_zero_sized()) {
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
