use std::{
    ffi::OsString,
    io::{Read, Write},
    path::PathBuf,
};

use alumina_boot_derive::AstSerializable;
use once_cell::unsync::OnceCell;

use crate::{
    ast::AstCtx,
    common::{Allocatable, AluminaError, ArenaAllocatable, FileId, HashMap, HashSet},
    global_ctx::{self, GlobalCtx},
    name_resolution::{
        path::Path,
        scope::{Scope, ScopeType},
    },
};

use thiserror::Error;

use super::{AstId, Item, ItemCell, ItemP};

#[derive(Error, Debug)]
pub enum Error {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("malformed ast")]
    Malformed,
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait AstSerializable<'a>: Sized
where
    Self: Sized,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'a, W>) -> Result<()>;
    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'a, R>) -> Result<Self>;
}

macro_rules! impl_serdes_for_primitive {
    ($uty:ty, $sty:ty, $write_func:ident, $read_func:ident) => {
        impl<'a> AstSerializable<'a> for $uty {
            fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'a, W>) -> Result<()> {
                serializer.$write_func(*self)
            }

            fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'a, R>) -> Result<Self> {
                deserializer.$read_func()
            }
        }

        impl<'a> AstSerializable<'a> for $sty {
            fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'a, W>) -> Result<()> {
                serializer.$write_func(*self as $uty)
            }

            fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'a, R>) -> Result<Self> {
                Ok(deserializer.$read_func()? as $sty)
            }
        }
    };
}

impl_serdes_for_primitive!(u8, i8, write_u8, read_u8);
impl_serdes_for_primitive!(u16, i16, write_u16, read_u16);
impl_serdes_for_primitive!(u32, i32, write_u32, read_u32);
impl_serdes_for_primitive!(u64, i64, write_u64, read_u64);
impl_serdes_for_primitive!(u128, i128, write_u128, read_u128);
impl_serdes_for_primitive!(usize, isize, write_usize, read_usize);

impl<'ast, T> AstSerializable<'ast> for Option<T>
where
    T: AstSerializable<'ast>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        match self {
            Some(v) => {
                serializer.write_u8(1)?;
                v.serialize(serializer)
            }
            None => {
                serializer.write_u8(0)?;
                Ok(())
            }
        }
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        match deserializer.read_u8()? {
            0 => Ok(None),
            1 => {
                let v = T::deserialize(deserializer)?;
                Ok(Some(v))
            }
            _ => unreachable!(),
        }
    }
}

impl<'ast> AstSerializable<'ast> for () {
    fn serialize<W: Write>(&self, _serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        Ok(())
    }

    fn deserialize<R: Read>(_deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        Ok(())
    }
}

impl<'a> AstSerializable<'a> for bool {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'a, W>) -> Result<()> {
        serializer.write_u8(*self as u8)
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'a, R>) -> Result<Self> {
        match deserializer.read_u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => unreachable!(),
        }
    }
}

macro_rules! impl_serdes_for_tuple {
    ( $( $name:ident )+ ) => {
        impl<'ast, $($name: AstSerializable<'ast>),+> AstSerializable<'ast> for ($($name,)+) {
            fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
                #[allow(non_snake_case)]
                let ($($name,)+) = self;
                $($name.serialize(serializer)?;)+
                Ok(())
            }

            fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
                Ok(($($name::deserialize(deserializer)?,)+))
            }
        }
    };
}

impl_serdes_for_tuple! { T1 }
impl_serdes_for_tuple! { T1 T2 }
impl_serdes_for_tuple! { T1 T2 T3 }
impl_serdes_for_tuple! { T1 T2 T3 T4 }
impl_serdes_for_tuple! { T1 T2 T3 T4 T5 }
impl_serdes_for_tuple! { T1 T2 T3 T4 T5 T6 }
impl_serdes_for_tuple! { T1 T2 T3 T4 T5 T6 T7 }

impl<'ast, T> AstSerializable<'ast> for &'ast T
where
    T: AstSerializable<'ast> + ArenaAllocatable<'ast, AstCtx<'ast>>,
    Self: From<<T as ArenaAllocatable<'ast, AstCtx<'ast>>>::ReturnType>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        (*self).serialize(serializer)
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let inner = T::deserialize(deserializer)?;

        Ok(inner.alloc_on(deserializer.ast).into())
    }
}

impl<'ast> AstSerializable<'ast> for &'ast str {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        serializer.write_bytes(self.as_bytes())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut bytes = vec![0; size];

        deserializer.read_bytes(&mut bytes[..])?;

        Ok(deserializer
            .ast
            .intern_str(std::str::from_utf8(&bytes[..]).unwrap()))
    }
}

impl<'ast> AstSerializable<'ast> for &'ast [u8] {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        serializer.write_bytes(self)
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut bytes = vec![0; size];

        deserializer.read_bytes(&mut bytes[..])?;

        Ok(deserializer.ast.arena.alloc_slice_copy(&bytes[..]))
    }
}

impl<'ast, T> AstSerializable<'ast> for &'ast [T]
where
    T: AstSerializable<'ast> + Allocatable,
    Vec<T>: ArenaAllocatable<'ast, AstCtx<'ast>>,
    Self: From<<Vec<T> as ArenaAllocatable<'ast, AstCtx<'ast>>>::ReturnType>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        for item in *self {
            item.serialize(serializer)?;
        }

        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(T::deserialize(deserializer)?);
        }

        Ok(vec.alloc_on(deserializer.ast).into())
    }
}

impl<'ast, T> AstSerializable<'ast> for Vec<T>
where
    T: AstSerializable<'ast>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        for item in self {
            item.serialize(serializer)?;
        }

        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(T::deserialize(deserializer)?);
        }

        Ok(vec)
    }
}

impl<'ast> AstSerializable<'ast> for String {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        serializer.write_usize(self.as_bytes().len())?;
        serializer.write_bytes(self.as_bytes())?;

        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut bytes = vec![0; size];

        deserializer.read_bytes(&mut bytes[..])?;

        Ok(String::from_utf8(bytes).unwrap())
    }
}

impl<'ast> AstSerializable<'ast> for PathBuf {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        let as_slice = self.to_str().unwrap();

        serializer.write_usize(as_slice.as_bytes().len())?;
        serializer.write_bytes(as_slice.as_bytes())?;

        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut bytes = vec![0; size];

        deserializer.read_bytes(&mut bytes[..])?;

        Ok(PathBuf::from(std::str::from_utf8(&bytes[..]).unwrap()))
    }
}

impl<'ast, T: AstSerializable<'ast>> AstSerializable<'ast> for OnceCell<T> {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        match self.get() {
            Some(v) => {
                serializer.write_u8(1)?;
                v.serialize(serializer)
            }
            None => {
                serializer.write_u8(0)?;
                Ok(())
            }
        }
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        match deserializer.read_u8()? {
            0 => Ok(OnceCell::new()),
            1 => {
                let v = T::deserialize(deserializer)?;
                Ok(OnceCell::from(v))
            }
            _ => unreachable!(),
        }
    }
}

pub struct AstSerializer<'ast, W: Write> {
    inner: W,
    seen_files: HashSet<FileId>,
    seen_ids: HashSet<AstId>,
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
            seen_files: HashSet::default(),
            seen_ids: HashSet::default(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn write_u8(&mut self, value: u8) -> Result<()> {
        let as_bytes = value.to_le_bytes();
        self.inner.write_all(&as_bytes)?;
        Ok(())
    }

    pub fn write_u16(&mut self, value: u16) -> Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_u32(&mut self, value: u32) -> Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_u64(&mut self, value: u64) -> Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_u128(&mut self, value: u128) -> Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_usize(&mut self, value: usize) -> Result<()> {
        write_varint!(self, value);
        Ok(())
    }

    pub fn write_bytes(&mut self, value: &'_ [u8]) -> Result<()> {
        self.inner.write_all(value)?;
        Ok(())
    }

    pub fn mark_file_seen(&mut self, file_id: FileId) {
        self.seen_files.insert(file_id);
    }

    pub fn mark_ast_id_seen(&mut self, ast_id: AstId) {
        self.seen_ids.insert(ast_id);
    }
}

pub struct AstDeserializer<'ast, R: std::io::Read> {
    pub global_ctx: GlobalCtx,
    pub ast: &'ast AstCtx<'ast>,
    ast_id_map: HashMap<AstId, AstId>,
    file_id_map: HashMap<FileId, FileId>,
    cell_map: HashMap<AstId, ItemP<'ast>>,
    inner: R,
}

macro_rules! read_varint {
    ($self:expr) => {{
        let mut value = 0;
        let mut shift = 0;

        // Type hint only
        #[inline(always)]
        fn _coerce<T>(value: T, _ref: T) -> T {
            value
        }

        loop {
            let mut byte = [0u8; 1];
            $self.inner.read_exact(&mut byte)?;
            let byte = byte[0];

            // TODO: This is a hack to get around the fact that we can't
            // use `as` on a generic type parameter.
            value |= _coerce((byte & 0x7F) as _, value) << shift;
            shift += 7;

            if byte & 0x80 == 0 {
                break;
            }
        }

        value
    }};
}

impl<'ast, R: std::io::Read> AstDeserializer<'ast, R> {
    pub fn new(global_ctx: GlobalCtx, ast: &'ast AstCtx<'ast>, inner: R) -> Self {
        Self {
            global_ctx,
            ast,
            inner,
            ast_id_map: HashMap::default(),
            file_id_map: HashMap::default(),
            cell_map: HashMap::default(),
        }
    }

    pub fn read_u8(&mut self) -> Result<u8> {
        let mut as_bytes = [0u8; 1];
        self.inner.read_exact(&mut as_bytes)?;
        Ok(u8::from_le_bytes(as_bytes))
    }

    pub fn read_u16(&mut self) -> Result<u16> {
        Ok(read_varint!(self))
    }

    pub fn read_u32(&mut self) -> Result<u32> {
        Ok(read_varint!(self))
    }

    pub fn read_u64(&mut self) -> Result<u64> {
        Ok(read_varint!(self))
    }

    pub fn read_u128(&mut self) -> Result<u128> {
        Ok(read_varint!(self))
    }

    pub fn read_usize(&mut self) -> Result<usize> {
        Ok(read_varint!(self))
    }

    pub fn read_bytes(&mut self, buf: &mut [u8]) -> Result<()> {
        self.inner.read_exact(buf)?;

        Ok(())
    }

    pub fn map_ast_id(&mut self, id: crate::ast::AstId) -> crate::ast::AstId {
        *self
            .ast_id_map
            .entry(id)
            .or_insert_with(|| self.ast.make_id())
    }

    pub fn map_file_id(&mut self, id: crate::ast::FileId) -> crate::ast::FileId {
        *self
            .file_id_map
            .entry(id)
            .or_insert_with(|| self.global_ctx.diag().make_file_id())
    }

    pub fn get_cell(&mut self, id: crate::ast::AstId) -> &'ast crate::ast::ItemCell<'ast> {
        let mapped = self.map_ast_id(id);
        self.cell_map
            .entry(mapped)
            .or_insert_with(|| self.ast.make_item())
    }
}

#[derive(AstSerializable)]
struct SerializedScope<'ast> {
    r#type: ScopeType,
    path: Path<'ast>,
    items: Vec<(&'ast str, ItemP<'ast>)>,
}

const MAGIC: &[u8] = b"\xa1\x00mina";

pub struct AstSaver<'ast> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    all_items: HashSet<ItemP<'ast>>,
    all_scopes: Vec<SerializedScope<'ast>>,
    version_string: &'static str,
}

impl<'ast> AstSaver<'ast> {
    pub fn new(
        version_string: &'static str,
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
    ) -> Self {
        Self {
            global_ctx,
            all_items: HashSet::default(),
            all_scopes: Vec::default(),
            ast,
            version_string,
        }
    }

    pub fn visit_scope<'src>(
        &mut self,
        scope: &Scope<'ast, 'src>,
    ) -> std::result::Result<(), AluminaError> {
        let mut items = Vec::default();
        for (name, item) in scope.inner().all_items() {
            if let Some(inner) = item.scope.as_ref() {
                self.visit_scope(inner)?;
            }

            let Some(item) = item.item() else { continue; };
            self.all_items.insert(item);

            let Some(name) = name else { continue; };
            items.push((name, item));
        }

        match scope.typ() {
            ScopeType::Root | ScopeType::StructLike | ScopeType::Protocol | ScopeType::Module => {
                self.all_scopes.push(SerializedScope {
                    r#type: scope.typ(),
                    path: scope.path().clone(),
                    items,
                });
            }

            ScopeType::Function
            | ScopeType::Macro
            | ScopeType::Closure
            | ScopeType::Impl
            | ScopeType::Enum
            | ScopeType::Block => {
                // those are not reachable via name resolution, so they don't need to be serialized
                // we still need to visit them though to collect all the items
            }
        }

        Ok(())
    }

    pub fn serialize<W: Write>(&mut self, mut writer: W) -> std::result::Result<(), AluminaError> {
        writer.write_all(MAGIC)?;
        writer.write_all(self.version_string.as_bytes())?;

        let mut serializer = AstSerializer::new(&mut writer);
        // First serialize all scopes
        self.all_scopes.serialize(&mut serializer)?;

        let defined_ids: HashSet<_> = self.all_items.iter().map(|item| item.id).collect();

        // Then the named items themselves
        serializer.write_usize(self.all_items.len())?;
        for item in self.all_items.iter() {
            item.id.serialize(&mut serializer)?;
            item.contents.serialize(&mut serializer)?;
        }

        // And finally the extra info (such as source filenames for spans in AST)
        let seen_files = serializer.seen_files.clone();
        let seen_ids = serializer.seen_ids.clone();

        serializer.write_usize(seen_files.len())?;

        for file_id in seen_files {
            let Some(filename) = self.global_ctx.diag().get_file_path(file_id) else { continue; };

            file_id.serialize(&mut serializer)?;
            filename.serialize(&mut serializer)?;
        }

        let lang_items = self.ast.lang_items.borrow();
        let lang_items: Vec<_> = lang_items
            .iter()
            .filter(|(_, item)| defined_ids.contains(&item.id))
            .collect();

        serializer.write_usize(lang_items.len())?;
        for (kind, lang_item) in lang_items {
            kind.serialize(&mut serializer)?;
            lang_item.id.serialize(&mut serializer)?;
        }

        let test_metadatas = self.ast.test_metadata.borrow();
        let test_metadatas: Vec<_> = test_metadatas
            .iter()
            .filter(|(item, _)| defined_ids.contains(&item.id))
            .collect();

        serializer.write_usize(test_metadatas.len())?;
        for (item, test_metadata) in test_metadatas {
            item.serialize(&mut serializer)?;
            test_metadata.serialize(&mut serializer)?;
        }

        Ok(())
    }
}
