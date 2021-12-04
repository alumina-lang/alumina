use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use super::IrCtx;
use crate::common::ArenaAllocatable;
use crate::{ast, common::AluminaError, ir};

pub struct MonoCtx<'ast, 'ir> {
    ir: &'ir ir::IrCtx<'ir>,
    id_map: HashMap<ast::AstId, ir::IrId>,
    finished: HashMap<MonomorphizeKey<'ast, 'ir>, ir::IRItemP<'ir>>,
}

impl<'ast, 'ir> MonoCtx<'ast, 'ir> {
    pub fn new(ir: &'ir ir::IrCtx<'ir>) -> Self {
        MonoCtx {
            ir,
            id_map: HashMap::new(),
            finished: HashMap::new(),
        }
    }

    fn map_id(&mut self, id: ast::AstId) -> ir::IrId {
        *self.id_map.entry(id).or_insert_with(|| self.ir.make_id())
    }

    pub fn into_inner(self) -> Vec<ir::IRItemP<'ir>> {
        self.finished.values().copied().collect()
    }
}

pub struct Monomorphizer<'a, 'ast, 'ir> {
    mono_ctx: &'a mut MonoCtx<'ast, 'ir>,
    replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphizeKey<'ast, 'ir>(ast::ItemP<'ast>, &'ir [ir::TyP<'ir>]);

impl<'a, 'ast, 'ir> Monomorphizer<'a, 'ast, 'ir> {
    pub fn new(mono_ctx: &'a mut MonoCtx<'ast, 'ir>) -> Self {
        Monomorphizer {
            mono_ctx,
            replacements: HashMap::new(),
        }
    }

    pub fn with_replacements<'b>(
        mono_ctx: &'b mut MonoCtx<'ast, 'ir>,
        replacements: HashMap<ast::AstId, ir::TyP<'ir>>,
    ) -> Monomorphizer<'b, 'ast, 'ir> {
        Monomorphizer {
            mono_ctx,
            replacements,
        }
    }

    fn monomorphize_item(
        &mut self,
        key: MonomorphizeKey<'ast, 'ir>,
    ) -> Result<ir::IRItemP<'ir>, AluminaError> {
        let item: ir::IRItemP = match self.mono_ctx.finished.entry(key.clone()) {
            // The cell may be empty at this point if we are dealing with cyclic dependencies
            // between types. In this case, we will just return the item as is, but it will not
            // be populated until the top-level item is finished.
            Entry::Occupied(entry) => return Ok(entry.get()),
            Entry::Vacant(entry) => entry.insert(self.mono_ctx.ir.make_symbol()),
        };

        let inner = match key.0.get() {
            ast::Item::Function(_) => unimplemented!(),
            ast::Item::Struct(s) => {
                if key.1.len() != s.placeholders.len() {
                    return Err(AluminaError::GenericParamCountMismatch(
                        s.placeholders.len(),
                        key.1.len(),
                    ));
                }

                let mut child = Self::with_replacements(
                    self.mono_ctx,
                    self.replacements
                        .iter()
                        .map(|(&k, &v)| (k, v))
                        .chain(
                            s.placeholders
                                .iter()
                                .zip(key.1.iter())
                                .map(|(&k, &v)| (k, v)),
                        )
                        .collect(),
                );

                let fields = s
                    .fields
                    .iter()
                    .map(|f| {
                        Ok(ir::Field {
                            name: f.name.alloc_on(child.mono_ctx.ir),
                            ty: child.monomorphize_type(f.ty)?,
                        })
                    })
                    .collect::<Result<Vec<_>, AluminaError>>()?;

                ir::IRItem::Struct(ir::Struct {
                    fields: fields.alloc_on(self.mono_ctx.ir),
                })
            }
        };
        item.assign(inner);

        Ok(item)
    }

    pub fn monomorphize_type(&mut self, typ: ast::TyP<'ast>) -> Result<ir::TyP<'ir>, AluminaError> {
        let result = match *typ {
            // TODO: can coalesce same usize == u64 depending on platform here I guess
            ast::Ty::Builtin(kind) => ir::Ty::Builtin(kind),
            ast::Ty::Array(inner, len) => ir::Ty::Array(self.monomorphize_type(inner)?, len),
            ast::Ty::Pointer(inner) => ir::Ty::Pointer(self.monomorphize_type(inner)?),
            ast::Ty::Slice(inner) => ir::Ty::Slice(self.monomorphize_type(inner)?),
            ast::Ty::Extern(id) => ir::Ty::Extern(self.mono_ctx.map_id(id)),
            ast::Ty::Function(args, ret) => ir::Ty::Function(
                args.iter()
                    .map(|arg| self.monomorphize_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir),
                self.monomorphize_type(ret)?,
            ),
            ast::Ty::Tuple(items) => ir::Ty::Tuple(
                items
                    .iter()
                    .map(|arg| self.monomorphize_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir),
            ),

            ast::Ty::Placeholder(id) => *self
                .replacements
                .get(&id)
                .copied()
                .expect("unbound placeholder"),

            ast::Ty::NamedType(item) => {
                let key = MonomorphizeKey(item, &[]);
                let item = self.monomorphize_item(key)?;
                ir::Ty::NamedType(item)
            }
            ast::Ty::GenericType(item, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.monomorphize_type(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .alloc_on(self.mono_ctx.ir);

                let key = MonomorphizeKey(item, args);
                let item = self.monomorphize_item(key)?;

                ir::Ty::NamedType(item)
            }
        };

        Ok(self.mono_ctx.ir.intern_type(result))
    }
}
