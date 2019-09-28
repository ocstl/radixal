//! Radixal provides the [`IntoDigits`](trait.IntoDigits.html) trait to simplify treating unsigned
//! integer types as a sequence of digits under a specified radix.
#![cfg_attr(not(feature = "std"), no_std)]

pub mod digits_iterator;

use core::num::Wrapping;
use digits_iterator::{DigitsIterator, RadixError};
use num_traits::{Unsigned, WrappingAdd, WrappingMul};

/// An extension trait on unsigned integer types (`u8`, `u16`, `u32`, `u64`, `u128` and `usize`)
/// and the corresponding `Wrapping` type.
pub trait IntoDigits: Copy + PartialOrd + Ord + WrappingAdd + WrappingMul + Unsigned {
    #[doc(hidden)]
    const BINARY_RADIX: Self;

    #[doc(hidden)]
    const DECIMAL_RADIX: Self;

    /// Creates a `DigitsIterator` with a given `radix`.
    ///
    /// Returns `Err(RadixError)` if the radix is 0 or 1.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let mut digits = 123_u32.into_digits(10).unwrap();
    ///
    /// assert_eq!(digits.next(), Some(1));
    /// assert_eq!(digits.next(), Some(2));
    /// assert_eq!(digits.next(), Some(3));
    /// assert_eq!(digits.next(), None);
    /// ```
    fn into_digits(self, radix: Self) -> Result<DigitsIterator<Self>, RadixError> {
        DigitsIterator::new(self, radix)
    }

    /// Creates a `DigitsIterator` with a binary radix.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let mut digits = 12_u32.into_binary_digits();
    ///
    /// assert_eq!(digits.next(), Some(1));
    /// assert_eq!(digits.next(), Some(1));
    /// assert_eq!(digits.next(), Some(0));
    /// assert_eq!(digits.next(), Some(0));
    /// assert_eq!(digits.next(), None);
    /// ```
    fn into_binary_digits(self) -> DigitsIterator<Self> {
        self.into_digits(Self::BINARY_RADIX).unwrap()
    }

    /// Creates a `DigitsIterator` with a decimal radix.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let mut digits = 12_u32.into_decimal_digits();
    ///
    /// assert_eq!(digits.next(), Some(1));
    /// assert_eq!(digits.next(), Some(2));
    /// assert_eq!(digits.next(), None);
    /// ```
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
    /// let n = 123_u32;
    /// assert_eq!(n.nbr_digits(10).unwrap(), 3);
    /// ```
    fn nbr_digits(self, radix: Self) -> Result<usize, RadixError> {
        self.into_digits(radix).map(DigitsIterator::count)
    }

    /// Counts the number of binary digits.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 12_u32;
    /// assert_eq!(n.nbr_binary_digits(), 4);
    /// ```
    fn nbr_binary_digits(self) -> usize {
        self.nbr_digits(Self::BINARY_RADIX).unwrap()
    }

    /// Counts the number of decimal digits.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 123_u32;
    ///
    /// assert_eq!(n.nbr_decimal_digits(), 3);
    /// ```
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
    /// let n = 123_u32;
    /// assert!(!n.is_palindrome(10).unwrap());
    /// let n = 121_u32;
    /// assert!(n.is_palindrome(10).unwrap());
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
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 12_u32;
    /// assert!(!n.is_binary_palindrome());
    /// let n = 9_u32;
    /// assert!(n.is_binary_palindrome());
    /// ```
    fn is_binary_palindrome(self) -> bool {
        self.is_palindrome(Self::BINARY_RADIX).unwrap()
    }

    /// Checks if it is a palindrome under a decimal number system.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 123_u32;
    /// assert!(!n.is_decimal_palindrome());
    /// let n = 121_u32;
    /// assert!(n.is_decimal_palindrome());
    /// ```
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
    /// let n = 123_u32;
    /// let reversed = n.reverse_digits(10).unwrap();
    /// assert_eq!(reversed, 321);
    ///
    /// /// Wrapping on overflow.
    /// let n = 255_u8;
    /// let reversed = n.reverse_digits(10).unwrap();
    /// assert_ne!(reversed, n);
    /// assert_eq!(reversed, 40);
    ///
    /// /// Trailing zeroes lead to irreversibility.
    /// let n = 1230_u32;
    /// let twice_reversed = n.reverse_digits(10).unwrap().reverse_digits(10).unwrap();
    /// assert_ne!(twice_reversed, n);
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
    /// let n = 123_u32;
    /// let reversed = n.reverse_decimal_digits();
    /// assert_eq!(reversed, 321);
    /// ```
    fn reverse_decimal_digits(self) -> Self {
        self.reverse_digits(Self::DECIMAL_RADIX).unwrap()
    }

    /// Tests if `self` and `other` are composed of the same digits under a given radix.
    ///
    /// Since any number can be left-padded with `0`'s, these are ignored when doing the
    /// comparison.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 120_u32;
    /// let m = 2100_u32;
    ///
    /// assert!(n.is_permutation(m, 10).unwrap());
    /// ```
    #[cfg(feature = "std")]
    fn is_permutation(self, other: Self, radix: Self) -> Result<bool, RadixError> {
        // This is reasonably efficient, but can be improved by short-circuiting.
        let mut a: Vec<Self> = self.into_digits(radix)?.filter(|&n| !n.is_zero()).collect();
        let mut b: Vec<Self> = other
            .into_digits(radix)?
            .filter(|&n| !n.is_zero())
            .collect();

        if a.len() != b.len() {
            return Ok(false);
        }

        a.sort();
        b.sort();
        Ok(a == b)
    }

    /// Tests if `self` and `other` are composed of the same digits under a decimal radix.
    ///
    /// Since any number can be left-padded with `0`'s, these are ignored when doing the
    /// comparison.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 120_u32;
    /// let m = 2100_u32;
    ///
    /// assert!(n.is_decimal_permutation(m).unwrap());
    /// ```
    #[cfg(feature = "std")]
    fn is_decimal_permutation(self, other: Self) -> Result<bool, RadixError> {
        // This is reasonably efficient, but can be improved by short-circuiting.
        let mut a: Vec<Self> = self
            .into_decimal_digits()
            .filter(|&n| !n.is_zero())
            .collect();
        let mut b: Vec<Self> = other
            .into_decimal_digits()
            .filter(|&n| !n.is_zero())
            .collect();

        if a.len() != b.len() {
            return Ok(false);
        }

        a.sort();
        b.sort();
        Ok(a == b)
    }

    /// Tests if `self` and `other` are composed of the same digits under a binary radix.
    ///
    /// Since any number can be left-padded with `0`'s, these are ignored when doing the
    /// comparison.
    ///
    /// This convenience function is offered for the sake of completeness; consider using the
    /// `count_ones` method instead.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::IntoDigits;
    ///
    /// let n = 12_u32;
    /// let m = 17_u32;
    ///
    /// assert!(n.is_binary_permutation(m).unwrap());
    /// ```
    #[cfg(feature = "std")]
    fn is_binary_permutation(self, other: Self) -> Result<bool, RadixError> {
        // This is reasonably efficient, but can be improved by short-circuiting.
        let mut a: Vec<Self> = self
            .into_binary_digits()
            .filter(|&n| !n.is_zero())
            .collect();
        let mut b: Vec<Self> = other
            .into_binary_digits()
            .filter(|&n| !n.is_zero())
            .collect();

        if a.len() != b.len() {
            return Ok(false);
        }

        a.sort();
        b.sort();
        Ok(a == b)
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
