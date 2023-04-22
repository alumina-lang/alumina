use std::io::Write;

use crate::{ast::AstCtx, common::HashMap};

pub struct AstSerializer<'ast, W: Write> {
    inner: W,
    _marker: std::marker::PhantomData<&'ast ()>,
}

macro_rules! write_varint {
    ($self:expr, $value:expr) => {
        let mut value = $value;
        loop {
            let mut byte = (value & 0x7F) as u8;
            value >>= 7;

            if value != 0 {
                byte |= 0x80;
            }

            $self.write_u8(byte)?;

            if value == 0 {
                break;
            }
        }
    };
}

impl<'ast, W: Write> AstSerializer<'ast, W> {
    pub fn new(inner: W) -> Self {
        Self {
            inner,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn write_u8(&mut self, value: u8) -> super::Result<()> {
        let as_bytes = value.to_le_bytes();
        self.inner.write_all(&as_bytes).map_err(|_| super::Error {})
    }

    pub fn write_u16(&mut self, value: u16) -> super::Result<()> {
        let as_bytes = value.to_le_bytes();
        self.inner.write_all(&as_bytes).map_err(|_| super::Error {})
    }

    pub fn write_u32(&mut self, value: u32) -> super::Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_u64(&mut self, value: u64) -> super::Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_u128(&mut self, value: u128) -> super::Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_usize(&mut self, value: usize) -> super::Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_bytes(&mut self, value: &'_ [u8]) -> super::Result<()> {
        self.inner.write_all(value).map_err(|_| super::Error {})
    }
}

pub struct AstDeserializer<'ast, R: std::io::Read> {
    pub ast: &'ast AstCtx<'ast>,
    id_map: HashMap<crate::ast::AstId, crate::ast::AstId>,
    cell_map: HashMap<crate::ast::AstId, crate::ast::ItemP<'ast>>,
    inner: R,
}

macro_rules! read_varint {
    ($self:expr) => {{
        let mut value = 0;
        let mut shift = 0;

        // Type hint only
        #[inline]
        fn identity_with_ref<T>(value: T, _ref: T) -> T {
            value
        }

        loop {
            let mut byte = [0u8; 1];
            $self
                .inner
                .read_exact(&mut byte)
                .map_err(|_| super::Error {})?;
            let byte = byte[0];

            // TODO: This is a hack to get around the fact that we can't
            // use `as` on a generic type parameter.
            value |= identity_with_ref((byte & 0x7F) as _, value) << shift;
            shift += 7;

            if byte & 0x80 == 0 {
                break;
            }
        }

        value
    }};
}

impl<'ast, R: std::io::Read> AstDeserializer<'ast, R> {
    pub fn new(ast: &'ast AstCtx<'ast>, inner: R) -> Self {
        Self {
            ast,
            inner,
            id_map: HashMap::default(),
            cell_map: HashMap::default(),
        }
    }

    pub fn read_u8(&mut self) -> super::Result<u8> {
        let mut as_bytes = [0u8; 1];
        self.inner
            .read_exact(&mut as_bytes)
            .map_err(|_| super::Error {})?;
        Ok(u8::from_le_bytes(as_bytes))
    }

    pub fn read_u16(&mut self) -> super::Result<u16> {
        let mut as_bytes = [0u8; 2];
        self.inner
            .read_exact(&mut as_bytes)
            .map_err(|_| super::Error {})?;
        Ok(u16::from_le_bytes(as_bytes))
    }

    pub fn read_u32(&mut self) -> super::Result<u32> {
        Ok(read_varint!(self))
    }

    pub fn read_u64(&mut self) -> super::Result<u64> {
        Ok(read_varint!(self))
    }

    pub fn read_u128(&mut self) -> super::Result<u128> {
        Ok(read_varint!(self))
    }

    pub fn read_usize(&mut self) -> super::Result<usize> {
        Ok(read_varint!(self))
    }

    pub fn read_bytes(&mut self, buf: &mut [u8]) -> super::Result<()> {
        self.inner.read_exact(buf).map_err(|_| super::Error {})
    }

    pub fn map_id(&mut self, id: crate::ast::AstId) -> crate::ast::AstId {
        *self.id_map.entry(id).or_insert_with(|| self.ast.make_id())
    }

    pub fn get_cell(&mut self, id: crate::ast::AstId) -> &'ast crate::ast::ItemCell<'ast> {
        let mapped = self.map_id(id);
        self.cell_map
            .entry(mapped)
            .or_insert_with(|| self.ast.make_item())
    }
}
