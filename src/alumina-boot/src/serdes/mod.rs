use std::mem::MaybeUninit;

use once_cell::unsync::OnceCell;

use crate::ast::{AstId, ItemCell};

pub struct Error {}

pub type Result<T> = std::result::Result<T, Error>;

pub trait AstSerializer<'a> {
    fn write_u8(&mut self, value: u8) -> Result<()>;
    fn write_u16(&mut self, value: u16) -> Result<()>;
    fn write_u32(&mut self, value: u32) -> Result<()>;
    fn write_u64(&mut self, value: u64) -> Result<()>;
    fn write_u128(&mut self, value: u128) -> Result<()>;
    fn write_usize(&mut self, value: usize) -> Result<()>;
    fn write_bytes(&mut self, value: &'_ [u8]) -> Result<()>;

    fn map_id(&mut self, id: AstId) -> AstId;
}

pub trait AstDeserializer<'a> {
    fn read_u8(&mut self) -> Result<u8>;
    fn read_u16(&mut self) -> Result<u16>;
    fn read_u32(&mut self) -> Result<u32>;
    fn read_u64(&mut self) -> Result<u64>;
    fn read_u128(&mut self) -> Result<u128>;
    fn read_usize(&mut self) -> Result<usize>;
    fn read_bytes(&mut self, buf: &'_ mut [u8]) -> Result<()>;

    fn alloc_slice<T>(&mut self, size: usize) -> &'a mut [T];
    fn alloc<T>(&mut self, val: T) -> &'a T;

    fn get_cell(&mut self, id: AstId) -> &'a ItemCell<'a>;
    fn map_id(&mut self, id: AstId) -> AstId;
}

pub trait AstSerializable<'a>: Sized
where
    Self: Sized,
{
    fn serialize<S: AstSerializer<'a>>(&self, serializer: &mut S) -> Result<()>;
    fn deserialize<D: AstDeserializer<'a>>(deserializer: &mut D) -> Result<Self>;
}

macro_rules! impl_serdes_for_primitive {
    ($uty:ty, $sty:ty, $write_func:ident, $read_func:ident) => {
        impl<'a> AstSerializable<'a> for $uty {
            fn serialize<S: AstSerializer<'a>>(&self, serializer: &mut S) -> Result<()> {
                serializer.$write_func(*self)
            }

            fn deserialize<D: AstDeserializer<'a>>(deserializer: &mut D) -> Result<Self> {
                deserializer.$read_func()
            }
        }

        impl<'a> AstSerializable<'a> for $sty {
            fn serialize<S: AstSerializer<'a>>(&self, serializer: &mut S) -> Result<()> {
                serializer.$write_func(*self as $uty)
            }

            fn deserialize<D: AstDeserializer<'a>>(deserializer: &mut D) -> Result<Self> {
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

impl<'lif, T> AstSerializable<'lif> for Option<T>
where
    T: AstSerializable<'lif>,
{
    fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
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

    fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
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

impl<'a> AstSerializable<'a> for () {
    fn serialize<S: AstSerializer<'a>>(&self, _serializer: &mut S) -> Result<()> {
        Ok(())
    }

    fn deserialize<D: AstDeserializer<'a>>(_deserializer: &mut D) -> Result<Self> {
        Ok(())
    }
}

impl<'a> AstSerializable<'a> for bool {
    fn serialize<S: AstSerializer<'a>>(&self, serializer: &mut S) -> Result<()> {
        serializer.write_u8(*self as u8)
    }

    fn deserialize<D: AstDeserializer<'a>>(deserializer: &mut D) -> Result<Self> {
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
            fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
                #[allow(non_snake_case)]
                let ($($name,)+) = self;
                $($name.serialize(serializer)?;)+
                Ok(())
            }

            fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
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

impl<'lif, T: AstSerializable<'lif>> AstSerializable<'lif> for &'lif T {
    fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
        (*self).serialize(serializer)
    }

    fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
        let inner = T::deserialize(deserializer)?;

        Ok(deserializer.alloc(inner))
    }
}

impl<'lif> AstSerializable<'lif> for &'lif str {
    fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
        serializer.write_usize(self.len())?;
        serializer.write_bytes(self.as_bytes())
    }

    fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let bytes = deserializer.alloc_slice(size);

        deserializer.read_bytes(bytes)?;

        Ok(std::str::from_utf8(bytes).unwrap())
    }
}

impl<'lif, T: AstSerializable<'lif>> AstSerializable<'lif> for &'lif [T] {
    fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
        serializer.write_usize(self.len())?;
        for item in *self {
            item.serialize(serializer)?;
        }

        Ok(())
    }

    fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
        let size = deserializer.read_usize()?;
        let slice = deserializer.alloc_slice(size);

        for item in slice.iter_mut() {
            *item = T::deserialize(deserializer)?;
        }

        Ok(slice)
    }
}

impl<'lif, T: AstSerializable<'lif>, const SIZE: usize> AstSerializable<'lif> for [T; SIZE]
where
    T: Copy,
{
    fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
        for item in *self {
            item.serialize(serializer)?;
        }
        Ok(())
    }

    fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
        let mut ret: [MaybeUninit<T>; SIZE] = unsafe { MaybeUninit::uninit().assume_init() };

        for item in &mut ret[..] {
            item.write(T::deserialize(deserializer)?);
        }

        Ok(unsafe { std::mem::transmute_copy(&ret) })
    }
}

impl<'lif, T: AstSerializable<'lif>> AstSerializable<'lif> for OnceCell<T> {
    fn serialize<S: AstSerializer<'lif>>(&self, serializer: &mut S) -> Result<()> {
        self.get().unwrap().serialize(serializer)
    }

    fn deserialize<D: AstDeserializer<'lif>>(deserializer: &mut D) -> Result<Self> {
        let inner = T::deserialize(deserializer)?;

        Ok(OnceCell::from(inner))
    }
}
