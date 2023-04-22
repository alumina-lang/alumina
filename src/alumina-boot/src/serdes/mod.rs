pub mod protocol;

use std::{
    io::{Read, Write},
    mem::MaybeUninit,
};

use once_cell::unsync::OnceCell;

use crate::{
    ast::{AstCtx, AstId, ItemCell},
    common::{Allocatable, ArenaAllocatable},
};

use self::protocol::{AstDeserializer, AstSerializer};

#[derive(Debug)]
pub struct Error {}

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

// impl_serdes_for_primitive!(u8, i8, write_u8, read_u8);
impl_serdes_for_primitive!(u16, i16, write_u16, read_u16);
impl_serdes_for_primitive!(u32, i32, write_u32, read_u32);
impl_serdes_for_primitive!(u64, i64, write_u64, read_u64);
impl_serdes_for_primitive!(u128, i128, write_u128, read_u128);
impl_serdes_for_primitive!(usize, isize, write_usize, read_usize);

impl<'lif, T> AstSerializable<'lif> for Option<T>
where
    T: AstSerializable<'lif>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
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

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
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

impl<'lif> AstSerializable<'lif> for () {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
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
        impl<'lif, $($name: AstSerializable<'lif>),+> AstSerializable<'lif> for ($($name,)+) {
            fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
                #[allow(non_snake_case)]
                let ($($name,)+) = self;
                $($name.serialize(serializer)?;)+
                Ok(())
            }

            fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
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

impl<'lif, T> AstSerializable<'lif> for &'lif T
where
    T: AstSerializable<'lif> + ArenaAllocatable<'lif, AstCtx<'lif>>,
    Self: From<<T as ArenaAllocatable<'lif, AstCtx<'lif>>>::ReturnType>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
        (*self).serialize(serializer)
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
        let inner = T::deserialize(deserializer)?;

        Ok(inner.alloc_on(&deserializer.ast).into())
    }
}

impl<'lif> AstSerializable<'lif> for &'lif str {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        serializer.write_bytes(self.as_bytes())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut bytes = vec![0; size];

        deserializer.read_bytes(&mut bytes[..])?;

        Ok(deserializer
            .ast
            .intern_str(std::str::from_utf8(&bytes[..]).unwrap()))
    }
}

impl<'lif> AstSerializable<'lif> for &'lif [u8] {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        serializer.write_bytes(self)
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut bytes = vec![0; size];

        deserializer.read_bytes(&mut bytes[..])?;

        Ok(deserializer.ast.arena.alloc_slice_copy(&bytes[..]))
    }
}

impl<'lif, T> AstSerializable<'lif> for &'lif [T]
where
    T: AstSerializable<'lif> + Allocatable,
    Vec<T>: ArenaAllocatable<'lif, AstCtx<'lif>>,
    Self: From<<Vec<T> as ArenaAllocatable<'lif, AstCtx<'lif>>>::ReturnType>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        for item in *self {
            item.serialize(serializer)?;
        }

        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(T::deserialize(deserializer)?);
        }

        Ok(vec.alloc_on(&deserializer.ast).into())
    }
}

impl<'lif, T> AstSerializable<'lif> for Vec<T>
where
    T: AstSerializable<'lif>,
{
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
        serializer.write_usize(self.len())?;
        for item in self {
            item.serialize(serializer)?;
        }

        Ok(())
    }

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let mut vec = Vec::with_capacity(size);

        for _ in 0..size {
            vec.push(T::deserialize(deserializer)?);
        }

        Ok(vec)
    }
}

impl<'lif, T: AstSerializable<'lif>> AstSerializable<'lif> for OnceCell<T> {
    fn serialize<W: Write>(&self, serializer: &mut AstSerializer<'lif, W>) -> Result<()> {
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

    fn deserialize<R: Read>(deserializer: &mut AstDeserializer<'lif, R>) -> Result<Self> {
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
