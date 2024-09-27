use std::{
    cell::RefCell,
    io::{Read, Write},
    path::PathBuf,
    rc::Rc,
};

use alumina_boot_macros::AstSerializable;
use once_cell::unsync::OnceCell;

use crate::{
    ast::AstCtx,
    common::{
        Allocatable, AluminaError, ArenaAllocatable, CodeErrorBuilder, FileId, HashMap, HashSet,
    },
    diagnostics::{DiagnosticsStack, Override},
    global_ctx::GlobalCtx,
    src::{
        path::Path,
        scope::{NamedItem, NamedItemKind, Scope, ScopeType},
    },
};

use thiserror::Error;

use super::{lang::Lang, Id, Item, ItemP, Metadatum};

#[derive(Error, Debug)]
pub enum Error {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("malformed AST")]
    Malformed,
    #[error("invalid AST magic number")]
    InvalidMagicNumber,
    #[error("incompatible AST version")]
    IncompatibleVersion,
    #[error("AST serialized with different --cfg options (expected: [{0}], actual: [{1}])")]
    IncompatibleCfgs(String, String),
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

impl<'ast, T> AstSerializable<'ast> for Box<T>
where
    T: AstSerializable<'ast>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'ast, W>) -> Result<()> {
        <T as AstSerializable<'ast>>::serialize(&**self, serializer)?;
        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'ast, R>) -> Result<Self> {
        Ok(Box::new(T::deserialize(deserializer)?))
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
}

struct DeserializeContextInner<'ast> {
    ast_id_map: HashMap<Id, Id>,
    file_id_map: HashMap<FileId, FileId>,
    cell_map: HashMap<Id, ItemP<'ast>>,
}

#[derive(Clone)]
pub struct DeserializeContext<'ast> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    inner: Rc<RefCell<DeserializeContextInner<'ast>>>,
}

impl<'ast> DeserializeContext<'ast> {
    pub fn new(global_ctx: GlobalCtx, ast: &'ast AstCtx<'ast>) -> Self {
        Self {
            inner: Rc::new(RefCell::new(DeserializeContextInner {
                ast_id_map: HashMap::default(),
                file_id_map: HashMap::default(),
                cell_map: HashMap::default(),
            })),
            global_ctx,
            ast,
        }
    }

    pub fn map_ast_id(&self, id: crate::ast::Id) -> crate::ast::Id {
        let mut inner = self.inner.borrow_mut();
        *inner
            .ast_id_map
            .entry(id)
            .or_insert_with(|| self.ast.make_id())
    }

    pub fn map_file_id(&self, id: crate::ast::FileId) -> crate::ast::FileId {
        let mut inner = self.inner.borrow_mut();
        *inner
            .file_id_map
            .entry(id)
            .or_insert_with(|| self.global_ctx.diag().make_file_id())
    }

    pub fn get_cell(&self, id: crate::ast::Id) -> &'ast crate::ast::ItemCell<'ast> {
        let mut inner = self.inner.borrow_mut();

        inner
            .cell_map
            .entry(id)
            .or_insert_with(|| self.ast.make_item_with(id))
    }
}

pub struct AstDeserializer<'ast, R: std::io::Read> {
    #[allow(dead_code)]
    pub global_ctx: GlobalCtx,
    pub ast: &'ast AstCtx<'ast>,
    context: DeserializeContext<'ast>,
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
    pub fn new(
        global_ctx: GlobalCtx,
        deserialize_context: DeserializeContext<'ast>,
        ast: &'ast AstCtx<'ast>,
        inner: R,
    ) -> Self {
        Self {
            global_ctx,
            ast,
            inner,
            context: deserialize_context,
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

    pub fn context(&self) -> DeserializeContext<'ast> {
        self.context.clone()
    }
}

#[derive(AstSerializable, Debug)]
struct SerializedItem<'ast> {
    name: &'ast str,
    kind: NamedItemKind<'ast>,
    scope: Option<SerializedScope<'ast>>,
}

#[derive(AstSerializable, Debug)]
struct SerializedScope<'ast> {
    r#type: ScopeType,
    path: Path<'ast>,
    items: Vec<SerializedItem<'ast>>,
    star_imports: Vec<Path<'ast>>,
}

impl<'ast> SerializedScope<'ast> {
    fn rehydrate<'src>(
        self,
        diag: &DiagnosticsStack,
        target: &Scope<'ast, 'src>,
    ) -> std::result::Result<(), AluminaError> {
        for item in self.items {
            let child_scope = if let Some(inner) = item.scope {
                let child_scope = target.named_child(inner.r#type, item.name);
                inner.rehydrate(diag, &child_scope)?;
                Some(child_scope)
            } else {
                None
            };

            target
                .add_item(
                    Some(item.name),
                    NamedItem::new_no_node(item.kind, child_scope),
                )
                .with_backtrace(diag)?;
        }

        for import in self.star_imports {
            target.add_star_import(import);
        }

        Ok(())
    }
}

const MAGIC: &[u8] = b"\xa1\x00mina";

pub struct AstSaver<'ast> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    all_items: HashSet<ItemP<'ast>>,
    all_scopes: Vec<SerializedScope<'ast>>,
    version_string: &'static [u8],
}

impl<'ast> AstSaver<'ast> {
    pub fn new(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        version_string: &'static [u8],
    ) -> Self {
        Self {
            global_ctx,
            all_items: HashSet::default(),
            all_scopes: Vec::default(),
            ast,
            version_string,
        }
    }

    pub fn add_scope<'src>(
        &mut self,
        scope: &Scope<'ast, 'src>,
    ) -> std::result::Result<(), AluminaError> {
        if let Some(scope) = self.serialize_scope(scope)? {
            self.all_scopes.push(scope);
        }

        Ok(())
    }

    fn serialize_scope<'src>(
        &mut self,
        scope: &Scope<'ast, 'src>,
    ) -> std::result::Result<Option<SerializedScope<'ast>>, AluminaError> {
        let mut items = Vec::default();
        let inner = scope.inner();
        for (name, named_item) in inner.all_items() {
            let inner_scope = if let Some(inner) = named_item.scope.as_ref() {
                self.serialize_scope(inner)?
            } else {
                None
            };

            if let Some(item) = named_item.item() {
                self.all_items.insert(item);
            }

            if let Some(name) = name {
                items.push(SerializedItem {
                    name,
                    kind: named_item.kind.clone(),
                    scope: inner_scope,
                });
            }
            // TODO: Resolve aliases
        }

        match scope.typ() {
            ScopeType::Root | ScopeType::StructLike | ScopeType::Protocol | ScopeType::Module => {
                Ok(Some(SerializedScope {
                    r#type: scope.typ(),
                    path: scope.path().clone(),
                    star_imports: inner.star_imports().cloned().collect(),
                    items,
                }))
            }

            ScopeType::Function
            | ScopeType::Macro
            | ScopeType::Closure
            | ScopeType::Impl
            | ScopeType::Enum
            | ScopeType::Block => {
                // those are not reachable via name resolution, so they don't need to be serialized
                // we still need to visit them though to collect all the items
                Ok(None)
            }
        }
    }

    pub fn save<W: Write>(&mut self, mut writer: W) -> Result<()> {
        writer.write_all(MAGIC)?;
        writer.write_all(self.version_string)?;

        let mut serializer = AstSerializer::new(&mut writer);
        // First serialize all scopes

        self.global_ctx.cfgs().serialize(&mut serializer)?;
        self.all_scopes.serialize(&mut serializer)?;

        let defined_ids: HashSet<_> = self.all_items.iter().map(|item| item.id).collect();

        // Then the named items themselves
        serializer.write_usize(self.all_items.len())?;
        for item in self.all_items.iter() {
            item.id.serialize(&mut serializer)?;
            item.contents.serialize(&mut serializer)?;
        }

        // And finally the extra info (such as source filenames for spans in AST)
        let local_names: Vec<_> = self
            .all_items
            .iter()
            .filter_map(|item| Some(item.id).zip(self.ast.local_name(item.id)))
            .collect();

        local_names.serialize(&mut serializer)?;

        let seen_files = serializer.seen_files.clone();
        serializer.write_usize(seen_files.len())?;

        for file_id in seen_files {
            let Some(filename) = self.global_ctx.diag().get_file_path(file_id) else {
                continue;
            };

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

        let metadata = self.ast.metadata.borrow();
        let metadata: Vec<_> = metadata
            .iter()
            .filter(|(item, _)| defined_ids.contains(&item.id))
            .collect();

        serializer.write_usize(metadata.len())?;
        for (item, metadatum) in metadata {
            item.serialize(&mut serializer)?;
            metadatum.serialize(&mut serializer)?;
        }

        self.global_ctx
            .diag()
            .overrides()
            .serialize(&mut serializer)?;

        Ok(())
    }
}

pub struct AstLoader<'ast> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    version_string: &'static [u8],
    context: DeserializeContext<'ast>,
}

impl<'ast> AstLoader<'ast> {
    pub fn new(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        version_string: &'static [u8],
    ) -> Self {
        Self {
            context: DeserializeContext::new(global_ctx.clone(), ast),
            global_ctx,
            ast,
            version_string,
        }
    }

    pub fn load<'src, R: Read>(
        &mut self,
        mut reader: R,
        root_scope: Scope<'ast, 'src>,
    ) -> std::result::Result<(), AluminaError> {
        let mut magic = [0; MAGIC.len()];
        reader.read_exact(&mut magic)?;

        if magic != MAGIC {
            return Err(Error::InvalidMagicNumber.into());
        }

        let mut version = [0; 512];
        match reader.read_exact(&mut version[..self.version_string.len()]) {
            Ok(()) if &version[..self.version_string.len()] == self.version_string => {}
            Err(e) if e.kind() != std::io::ErrorKind::UnexpectedEof => return Err(e.into()),
            _ => return Err(Error::IncompatibleVersion.into()),
        }

        let mut deserializer = AstDeserializer::new(
            self.global_ctx.clone(),
            self.context.clone(),
            self.ast,
            &mut reader,
        );
        let cfgs: Vec<(String, Option<String>)> = Vec::deserialize(&mut deserializer)?;
        if cfgs != self.global_ctx.cfgs() {
            fn render(cfgs: impl IntoIterator<Item = (String, Option<String>)>) -> String {
                cfgs.into_iter()
                    .map(|(k, v)| match v {
                        Some(v) => format!("{}={}", k, v),
                        None => k,
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            }

            return Err(
                Error::IncompatibleCfgs(render(self.global_ctx.cfgs()), render(cfgs)).into(),
            );
        }

        let num_scopes = deserializer.read_usize()?;
        let diag = DiagnosticsStack::new(self.global_ctx.diag().clone());
        for _ in 0..num_scopes {
            let scope: SerializedScope = SerializedScope::deserialize(&mut deserializer)?;
            let target = root_scope
                .ensure_module(scope.path.clone(), scope.r#type)
                .with_backtrace(&diag)?;

            scope.rehydrate(&diag, &target)?;
        }

        let num_items = deserializer.read_usize()?;
        for _ in 0..num_items {
            let id = Id::deserialize(&mut deserializer)?;
            let contents = OnceCell::<Item>::deserialize(&mut deserializer)?;

            if let Some(contents) = contents.into_inner() {
                self.context.get_cell(id).assign(contents);
            }
        }

        let num_local_names = deserializer.read_usize()?;
        for _ in 0..num_local_names {
            let id = Id::deserialize(&mut deserializer)?;
            let name = <&'ast str as AstSerializable<'ast>>::deserialize(&mut deserializer)?;

            self.ast.add_local_name(id, name);
        }

        let num_files = deserializer.read_usize()?;
        for _ in 0..num_files {
            let file_id = FileId::deserialize(&mut deserializer)?;
            let filename = PathBuf::deserialize(&mut deserializer)?;

            self.global_ctx.diag().add_file(file_id, filename);
        }

        let num_lang_items = deserializer.read_usize()?;
        for _ in 0..num_lang_items {
            let kind = Lang::deserialize(&mut deserializer)?;
            let id = Id::deserialize(&mut deserializer)?;

            self.ast.add_lang_item(kind, self.context.get_cell(id))
        }

        let num_metadata = deserializer.read_usize()?;
        for _ in 0..num_metadata {
            let item = Id::deserialize(&mut deserializer)?;
            let metadatum = Metadatum::deserialize(&mut deserializer)?;

            self.ast
                .add_metadatum(self.context.get_cell(item), metadatum);
        }

        let overrides: Vec<Override> = Vec::deserialize(&mut deserializer)?;
        for r#override in overrides {
            self.global_ctx.diag().add_override(r#override);
        }

        Ok(())
    }
}
