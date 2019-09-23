use core::ops::{Div, Mul, Rem};

/// Trait to restrict implementations to primitive unsigned integer types with associated constants.
pub trait UnsignedInteger:
    Copy + PartialOrd + Mul<Output = Self> + Div<Output = Self> + Rem<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
}

macro_rules! impl_unsigned_integer {
    ( $($t:ty)* ) => {
        $(impl UnsignedInteger for $t {
            const ZERO: $t = 0;
            const ONE: $t = 1;
        })*
    };
}

impl_unsigned_integer!(u8 u16 u32 u64 u128 usize);
