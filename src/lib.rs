//! Radixal provides the [`IntoDigits`](trait.IntoDigits.html) trait to simplify treating unsigned
//! integer types as a sequence of digits under a specified radix.
#![no_std]

pub mod digits_iterator;

use core::num::Wrapping;
use digits_iterator::{DigitsIterator, RadixError};
use num_traits::{Unsigned, WrappingAdd, WrappingMul};

/// An extension trait on unsigned integer types (`u8`, `u16`, `u32`, `u64`, `u128` and `usize`)
/// and the corresponding `Wrapping` type.
///
/// # Example
///
/// ```
/// use radixal::IntoDigits;
///
/// let mut digits = 123_u32.into_digits(10).expect("Bad radix.");
///
/// assert_eq!(digits.next(), Some(1));
/// assert_eq!(digits.next(), Some(2));
/// assert_eq!(digits.next(), Some(3));
/// assert_eq!(digits.next(), None);
/// ```
pub trait IntoDigits: Copy + PartialOrd + WrappingAdd + WrappingMul + Unsigned {
    #[doc(hidden)]
    const BINARY_RADIX: Self;

    #[doc(hidden)]
    const DECIMAL_RADIX: Self;

    /// Creates a `DigitsIterator` with a given `radix`.
    ///
    /// Returns `Err(RadixError)` if the radix is 0 or 1.
    fn into_digits(self, radix: Self) -> Result<DigitsIterator<Self>, RadixError> {
        DigitsIterator::new(self, radix)
    }

    /// Creates a `DigitsIterator` with a binary radix.
    fn into_binary_digits(self) -> DigitsIterator<Self> {
        self.into_digits(Self::BINARY_RADIX).unwrap()
    }

    /// Creates a `DigitsIterator` with a decimal radix.
    fn into_decimal_digits(self) -> DigitsIterator<Self> {
        self.into_digits(Self::DECIMAL_RADIX).unwrap()
    }

    /// Counts the number of digits for a given `radix`.
    ///
    /// Returns `Err(RadixError)` if the radix is 0 or 1.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let number = 123_u32;
    /// assert_eq!(number.nbr_digits(10).unwrap(), 3);
    /// ```
    fn nbr_digits(self, radix: Self) -> Result<usize, RadixError> {
        self.into_digits(radix).map(DigitsIterator::count)
    }

    /// Counts the number of binary digits.
    fn nbr_binary_digits(self) -> usize {
        self.nbr_digits(Self::BINARY_RADIX).unwrap()
    }

    /// Counts the number of decimal digits.
    fn nbr_decimal_digits(self) -> usize {
        self.nbr_digits(Self::DECIMAL_RADIX).unwrap()
    }

    /// Checks if it is a palindrome for a given `radix`.
    ///
    /// Returns `Err(RadixError)` if the radix is 0 or 1.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let number = 123_u32;
    /// assert!(!number.is_palindrome(10).unwrap());
    /// let number = 121_u32;
    /// assert!(number.is_palindrome(10).unwrap());
    /// ```
    fn is_palindrome(self, radix: Self) -> Result<bool, RadixError> {
        let mut iter = self.into_digits(radix)?;

        while iter.len() > 1 {
            if iter.next() != iter.next_back() {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Checks if it is a palindrome under a binary number system.
    fn is_binary_palindrome(self) -> bool {
        self.is_palindrome(Self::BINARY_RADIX).unwrap()
    }

    /// Checks if it is a palindrome under a decimal number system.
    fn is_decimal_palindrome(self) -> bool {
        self.is_palindrome(Self::DECIMAL_RADIX).unwrap()
    }

    /// Reverses the digits, returning a new number with the digits reversed, using wrapping
    /// semantics if necessary.
    ///
    /// Since trailing zeroes are not conserved, this operation is not reversible.
    ///
    /// Returns `Err(RadixError)` if the radix is 0 or 1.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let number = 123_u32;
    /// let reversed = number.reverse_digits(10).unwrap();
    /// assert_eq!(reversed, 321);
    ///
    /// /// Wrapping on overflow.
    /// let number = 255_u8;
    /// let reversed = number.reverse_digits(10).unwrap();
    /// assert_ne!(reversed, number);
    /// assert_eq!(reversed, 40);
    ///
    /// /// Trailing zeroes lead to irreversibility.
    /// let number = 1230_u32;
    /// let twice_reversed = number.reverse_digits(10).unwrap().reverse_digits(10).unwrap();
    /// assert_ne!(twice_reversed, number);
    /// assert_eq!(twice_reversed, 123);
    /// ```
    fn reverse_digits(self, radix: Self) -> Result<Self, RadixError> {
        self.into_digits(radix)
            .map(DigitsIterator::into_reversed_number)
    }

    /// Reverse the digits under a binary number system.
    ///
    /// Since trailing zeroes are not conserved, this operation is not reversible.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 0b1100_u32;
    /// let m = n.reverse_binary_digits();
    ///
    /// assert_eq!(m, 0b11);
    /// ```
    fn reverse_binary_digits(self) -> Self {
        self.reverse_digits(Self::BINARY_RADIX).unwrap()
    }

    /// Reverses the digits under a decimal number system, using wrapping semantics if necessary.
    ///
    /// Since trailing zeroes are not conserved, this operation is not reversible.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let number = 123_u32;
    /// let reversed = number.reverse_decimal_digits();
    /// assert_eq!(reversed, 321);
    /// ```
    fn reverse_decimal_digits(self) -> Self {
        self.reverse_digits(Self::DECIMAL_RADIX).unwrap()
    }
}

macro_rules! impl_digits {
    ( $($t:ty)* ) => {
        $(
            impl IntoDigits for $t {
                const BINARY_RADIX: Self = 2;
                const DECIMAL_RADIX: Self = 10;
            }
            impl IntoDigits for Wrapping<$t> {
                const BINARY_RADIX: Self = Wrapping(2);
                const DECIMAL_RADIX: Self = Wrapping(10);
            }
        )*
    };
}

impl_digits!(u8 u16 u32 u64 u128 usize);

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
    fn test_nbr_digits() {
        let n = 54321_u32;
        assert_eq!(n.nbr_digits(10), Ok(5));
    }

    #[test]
    fn test_is_palindrome() {
        let n = 543_212_345_u32;
        assert!(n.is_palindrome(10).unwrap());
        let n = 54321_u32;
        assert!(!n.is_palindrome(10).unwrap());
        let n = 211_u32;
        assert!(!(n.is_palindrome(10).unwrap()));
    }
}
