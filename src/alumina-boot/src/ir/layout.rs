use crate::ast::{Attribute, BuiltinType};
use crate::common::{CodeDiagnostic, CycleGuardian};
use crate::global_ctx::GlobalCtx;
use crate::ir::{Item, ItemP, Ty, TyP};

use super::Closure;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PointerWidth {
    U32,
    U64,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Layout {
    pub size: usize,
    pub align: usize,
}

impl Layout {
    pub fn new(size: usize, align: usize) -> Self {
        Self { size, align }
    }

    pub fn default_zst() -> Self {
        Self::new(0, 1)
    }

    pub fn bool() -> Self {
        Self::new(1, 1)
    }

    pub fn padding(size: usize) -> Self {
        Self::new(size, 1)
    }

    pub fn integer(bit_width: usize) -> Self {
        Self::new(bit_width / 8, bit_width / 8)
    }

    pub fn pointer(pointer_size: PointerWidth) -> Self {
        match pointer_size {
            PointerWidth::U32 => Self::integer(32),
            PointerWidth::U64 => Self::integer(64),
        }
    }

    pub fn float(bit_width: usize) -> Self {
        Self::new(bit_width / 8, bit_width / 8)
    }

    pub fn array(&self, len: usize) -> Self {
        Self::new(self.size * len, self.align)
    }

    pub fn is_zero_sized(&self) -> bool {
        self.size == 0
    }

    pub fn is_compatible_with(&self, other: &Self) -> bool {
        self.size == other.size && self.align == other.align
    }
}

type FieldLayout<T> = (Layout, Vec<(Option<T>, Layout)>);

pub struct Layouter<'ir> {
    pointer_width: PointerWidth,
    cycle_guardian: CycleGuardian<ItemP<'ir>>,
}

impl<'ir> Layouter<'ir> {
    pub fn new(global_ctx: GlobalCtx) -> Self {
        let pointer_width = match global_ctx
            .cfg("target_pointer_width")
            .as_ref()
            .map(|s| s.as_deref())
        {
            Some(Some("64")) => PointerWidth::U64,
            Some(Some("32")) => PointerWidth::U32,
            _ => panic!("unsupported target_pointer_width"),
        };

        Self {
            pointer_width,
            cycle_guardian: CycleGuardian::new(),
        }
    }

    fn layout_of_aggregate<I>(
        &self,
        custom_align: Option<usize>,
        is_union: bool,
        is_packed: bool,
        fields: I,
    ) -> Result<Layout, CodeDiagnostic>
    where
        I: IntoIterator<Item = TyP<'ir>>,
    {
        let mut align = 1;
        let mut size = 0;

        for field_ty in fields {
            let field_layout = self.layout_of(field_ty)?;
            let field_align = if is_packed {
                field_layout.align.min(custom_align.unwrap_or(1))
            } else {
                field_layout.align
            };

            align = align.max(field_align);
            if is_union {
                size = size.max(field_layout.size);
            } else {
                size = (size + field_align - 1) / field_align * field_align; // add padding between fields
                size += field_layout.size;
            }
        }

        if !is_packed {
            align = align.max(custom_align.unwrap_or(1));
        }

        size = (size + align - 1) / align * align; // add padding at the end

        Ok(Layout::new(size, align))
    }

    pub fn field_layout_of_aggregate<I, T>(
        &self,
        custom_align: Option<usize>,
        is_union: bool,
        is_packed: bool,
        fields: I,
    ) -> Result<FieldLayout<T>, CodeDiagnostic>
    where
        I: IntoIterator<Item = (T, TyP<'ir>)>,
    {
        let mut result = Vec::new();

        let mut align = 1;
        let mut size = 0;

        for (elem, field_ty) in fields {
            let field_layout = self.layout_of(field_ty)?;
            let field_align = if is_packed {
                field_layout.align.min(custom_align.unwrap_or(1))
            } else {
                field_layout.align
            };

            align = align.max(field_align);
            if is_union {
                size = size.max(field_layout.size);
            } else {
                let padding_size = (size + field_align - 1) / field_align * field_align - size;
                if padding_size > 0 {
                    result.push((None, Layout::padding(padding_size)));
                }
                size += padding_size + field_layout.size;
            }

            result.push((Some(elem), field_layout));
        }

        if !is_packed {
            align = align.max(custom_align.unwrap_or(1));
        }

        let final_size = (size + align - 1) / align * align;
        if final_size > size {
            if is_union {
                result.push((None, Layout::padding(final_size)));
            } else {
                result.push((None, Layout::padding(final_size - size)));
            }
        }

        Ok((Layout::new(final_size, align), result))
    }

    pub fn layout_of_item(&self, item: ItemP<'ir>) -> Result<Layout, CodeDiagnostic> {
        let _guard = self
            .cycle_guardian
            .guard(item)
            .map_err(|_| CodeDiagnostic::TypeWithInfiniteSize)?;

        let ret = match item.get()? {
            Item::StructLike(s) | Item::Closure(Closure { data: s, .. }) => {
                let mut custom_align = None;
                let mut is_packed = false;

                for attr in s.attributes {
                    match attr {
                        Attribute::Align(a) => custom_align = Some(*a),
                        Attribute::Packed(a) => {
                            custom_align = Some(*a);
                            is_packed = true;
                        }
                        Attribute::Transparent => {}
                        _ => {}
                    }
                }
                self.layout_of_aggregate(
                    custom_align,
                    s.is_union,
                    is_packed,
                    s.fields.iter().map(|f| f.ty),
                )?
            }
            Item::Alias(i) => self.layout_of(i)?,
            Item::Enum(e) => self.layout_of(e.underlying_ty)?,
            Item::Protocol(_) | Item::Function(_) | Item::Static(_) | Item::Const(_) => {
                Layout::default_zst()
            }
        };

        Ok(ret)
    }

    pub fn layout_of(&self, ty: TyP<'ir>) -> Result<Layout, CodeDiagnostic> {
        match ty {
            Ty::Array(inner, len) => {
                let inner_layout = self.layout_of(inner)?;
                Ok(inner_layout.array(*len))
            }
            Ty::Builtin(kind) => match kind {
                BuiltinType::Never => Ok(Layout::default_zst()),
                BuiltinType::Bool => Ok(Layout::bool()),
                BuiltinType::U8 | BuiltinType::I8 => Ok(Layout::integer(8)),
                BuiltinType::U16 | BuiltinType::I16 => Ok(Layout::integer(16)),
                BuiltinType::U32 | BuiltinType::I32 => Ok(Layout::integer(32)),
                BuiltinType::U64 | BuiltinType::I64 => Ok(Layout::integer(64)),
                BuiltinType::U128 | BuiltinType::I128 => Ok(Layout::integer(128)),
                BuiltinType::USize | BuiltinType::ISize => Ok(Layout::pointer(self.pointer_width)),
                BuiltinType::F32 => Ok(Layout::float(32)),
                BuiltinType::F64 => Ok(Layout::float(64)),
            },

            Ty::Pointer(_, _) => Ok(Layout::pointer(self.pointer_width)),
            Ty::FunctionPointer(_, _) => Ok(Layout::pointer(self.pointer_width)),
            Ty::Tuple(elems) => self.layout_of_aggregate(None, false, false, elems.iter().copied()),
            Ty::Item(item) => self.layout_of_item(item),
        }
    }
}
