//! Radixal provides the [`AsDigits`](trait.AsDigits.html) trait to simplify treating unsigned
//! integer types as a sequence of digits under a specified radix.

#![no_std]

pub mod digits;
pub mod traits;

use digits::{DigitsIterator, RadixError};

/// An extension trait on unsigned integer types (`u8`, `u16`, `u32`, `u64`, `u128` and `usize`).
///
/// The [`into_digits`](#into_digits) method creates an `Iterator<Item = T>` over the digits of the
/// number, in big endian order, i.e. from most significant to least significant. Since
/// [`DigitsIterator`](digits/struct.DigitsIterator.html) implements `DoubleEndedIterator`, this
/// order is easily reversed.
///
/// ```
/// use radixal::AsDigits;
///
/// let mut digits = 123_u32.into_digits(10).expect("Bad radix.");
///
/// assert_eq!(digits.next(), Some(1));
/// assert_eq!(digits.next(), Some(2));
/// assert_eq!(digits.next(), Some(3));
/// assert_eq!(digits.next(), None);
/// ```
pub trait AsDigits: traits::UnsignedInteger {
    fn into_digits(self, radix: Self) -> Result<DigitsIterator<Self>, RadixError>;

    fn to_digits(&self, radix: Self) -> Result<DigitsIterator<Self>, RadixError> {
        self.into_digits(radix)
    }
}

macro_rules! impl_digits {
    ($t:ty) => {
        impl AsDigits for $t {
            fn into_digits(self, radix: Self) -> Result<DigitsIterator<Self>, RadixError> {
                DigitsIterator::new(self, radix)
            }
        }
    };

    ($t:ty, $($ts:ty),+) => {
        impl_digits! { $t }
        impl_digits! { $($ts),+ }
    };
}

impl_digits!(u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn very_small() {
        let mut digits = 8_u32.into_digits(10).unwrap();
        assert_eq!(digits.len(), 1);
        assert_eq!(digits.next(), Some(8));
        assert_eq!(digits.next(), None);
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_big_endian() {
        let mut digits = 123_u32.into_digits(10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next(), Some(3));
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_little_endian_123() {
        let mut digits = 123_u64.into_digits(10).unwrap();

        assert_eq!(digits.next_back(), Some(3));
        assert_eq!(digits.next_back(), Some(2));
        assert_eq!(digits.next_back(), Some(1));
        assert_eq!(digits.next_back(), None);
    }

    #[test]
    fn test_reversible_iterator() {
        let mut digits = 123_u128.into_digits(10).unwrap().rev();

        assert_eq!(digits.next(), Some(3));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_large_number_u8() {
        let mut digits = 123_u8.into_digits(10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next_back(), Some(3));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next_back(), None);
    }

    #[test]
    fn test_to_digits() {
        let mut digits = 123_u32.to_digits(10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next(), Some(3));
        assert_eq!(digits.next(), None);
    }
}
