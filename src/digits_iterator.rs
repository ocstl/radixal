use crate::IntoDigits;

#[derive(Debug, PartialEq, Eq)]
pub enum RadixError {
    Radix0,
    Radix1,
}

/// An iterator over the digits of a number.
///
/// For a given radix, iterates over the digits in big endian order, i.e. from most significant
/// to least significant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigitsIterator<T: IntoDigits> {
    current: T,
    radix: T,
    splitter: T,
    len: usize,
}

impl<T: IntoDigits> DigitsIterator<T> {
    /// Create a new `DigitsIterator` for `number` using `radix`.
    ///
    /// Returns an `Err(RadixError)` if the radix is `0` is `1`.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::digits_iterator::{DigitsIterator, RadixError};
    ///
    /// let mut digits = DigitsIterator::new(123_u32, 10).unwrap();
    ///
    /// assert_eq!(digits.next(), Some(1));
    /// assert_eq!(digits.next(), Some(2));
    /// assert_eq!(digits.next(), Some(3));
    /// assert_eq!(digits.next(), None);
    ///
    /// let mut digits = DigitsIterator::new(123_u32, 0);
    /// assert_eq!(digits.unwrap_err(), RadixError::Radix0);
    ///
    /// let mut digits = DigitsIterator::new(123_u32, 1);
    /// assert_eq!(digits.unwrap_err(), RadixError::Radix1);
    /// ```
    pub fn new(number: T, radix: T) -> Result<DigitsIterator<T>, RadixError> {
        // Handle errors (radix too small) and the special case of 0.
        if radix == T::zero() {
            return Err(RadixError::Radix0);
        } else if radix == T::one() {
            return Err(RadixError::Radix1);
        } else if number.is_zero() {
            return Ok(DigitsIterator {
                current: number,
                radix,
                splitter: T::one(),
                len: 1,
            });
        }

        let mut len = 0;
        let mut splitter = T::one();
        let mut n = number;

        // Iterate until we reach the middle.
        while n >= splitter {
            len += 1;
            splitter = splitter * radix;
            n = n / radix;
        }

        // Then adjust for the remainder.
        let adjustment = splitter / radix;
        if n >= adjustment {
            splitter = splitter * adjustment;
            len += len;
        } else {
            splitter = adjustment * adjustment;
            len += len - 1;
        }

        Ok(DigitsIterator {
            current: number,
            radix,
            splitter,
            len,
        })
    }

    /// Converts the `DigitsIterator` into a number.
    pub fn into_number(self) -> T {
        self.current
    }

    /// Converts the `DigitsIterator` into a number with the digits reversed, using wrapping
    /// semantics if necessary.
    pub fn into_reversed_number(self) -> T {
        let radix = self.radix;
        self.rfold(T::zero(), |acc, digit| {
            acc.wrapping_mul(&radix).wrapping_add(&digit)
        })
    }

    /// Returns the current number being iterated over, leaving the iterator unchanged.
    pub fn to_number(&self) -> T {
        self.current
    }

    /// Returns the current number being iterated over with the digits reversed, leaving the
    /// iterator unchanged.
    pub fn to_reversed_number(&self) -> T {
        self.clone().rfold(T::zero(), |acc, digit| {
            acc.wrapping_mul(&self.radix).wrapping_add(&digit)
        })
    }

    /// Rotate the digits such that the first digit (most significant) becomes the last digit
    /// (least significant). This operation preserves the number of digits; in other words, the
    /// first digit may now be `0`.
    ///
    /// Since the new number may overflow, wrapping semantics are used.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::digits_iterator::DigitsIterator;
    ///
    /// let number = 1234_u32;
    /// let mut digits = DigitsIterator::new(number, 10).unwrap();
    ///
    /// assert_eq!(digits.rotate_left(1).to_number(), 2341);
    /// assert_eq!(digits.rotate_left(2).to_number(), 4123);
    /// ```
    pub fn rotate_left(&mut self, mut n: usize) -> &Self {
        while n > 0 {
            let first_digit = self.current / self.splitter;
            self.current = (self.current % self.splitter)
                .wrapping_mul(&self.radix)
                .wrapping_add(&first_digit);
            n -= 1;
        }

        self
    }

    /// Rotate the digits such that the last digit (least significant) becomes the first digit
    /// (most significant). This operation preserves the number of digits; in other words, the
    /// first digit may now be `0`.
    ///
    /// Since the new number may overflow, wrapping sematics are used.
    ///
    /// # Example
    ///
    /// ```
    /// use radixal::digits_iterator::DigitsIterator;
    ///
    /// let number = 1234_u32;
    /// let mut digits = DigitsIterator::new(number, 10).unwrap();
    ///
    /// assert_eq!(digits.rotate_right(1).to_number(), 4123);
    /// assert_eq!(digits.rotate_right(2).to_number(), 2341);
    /// ```
    pub fn rotate_right(&mut self, mut n: usize) -> &Self {
        while n > 0 {
            let last_digit = self.current % self.radix;
            self.current =
                (self.current / self.radix).wrapping_add(&last_digit.wrapping_mul(&self.splitter));
            n -= 1;
        }

        self
    }
}

impl<T: IntoDigits> Iterator for DigitsIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            let digit = self.current / self.splitter;
            self.current = self.current % self.splitter;
            self.splitter = self.splitter / self.radix;
            self.len -= 1;
            Some(digit)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn count(self) -> usize {
        self.len
    }

    fn last(self) -> Option<Self::Item> {
        if self.len > 0 {
            Some(self.current % self.radix)
        } else {
            None
        }
    }
}

impl<T: IntoDigits> DoubleEndedIterator for DigitsIterator<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            let digit = self.current % self.radix;
            self.current = self.current / self.radix;
            self.splitter = self.splitter / self.radix;
            self.len -= 1;
            Some(digit)
        }
    }
}

impl<T: IntoDigits> core::iter::FusedIterator for DigitsIterator<T> {}

impl<T: IntoDigits> ExactSizeIterator for DigitsIterator<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types() {
        use core::num::Wrapping;
        assert!(DigitsIterator::new(1_u8, 10).is_ok());
        assert!(DigitsIterator::new(1_u16, 10).is_ok());
        assert!(DigitsIterator::new(1_u32, 10).is_ok());
        assert!(DigitsIterator::new(1_u64, 10).is_ok());
        assert!(DigitsIterator::new(1_u128, 10).is_ok());
        assert!(DigitsIterator::new(1_usize, 10).is_ok());
        assert!(DigitsIterator::new(Wrapping(1_u8), Wrapping(10)).is_ok());
        assert!(DigitsIterator::new(Wrapping(1_u16), Wrapping(10)).is_ok());
        assert!(DigitsIterator::new(Wrapping(1_u32), Wrapping(10)).is_ok());
        assert!(DigitsIterator::new(Wrapping(1_u64), Wrapping(10)).is_ok());
        assert!(DigitsIterator::new(Wrapping(1_u128), Wrapping(10)).is_ok());
        assert!(DigitsIterator::new(Wrapping(1_usize), Wrapping(10)).is_ok());
    }

    #[test]
    fn very_small() {
        let mut digits = DigitsIterator::new(8_u32, 10_u32).unwrap();
        assert_eq!(digits.len(), 1);
        assert_eq!(digits.next(), Some(8));
        assert_eq!(digits.next(), None);
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_big_endian_123() {
        let mut digits = DigitsIterator::new(123_u32, 10).unwrap();
        assert_eq!(digits.len(), 3);

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next(), Some(3));
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_little_endian_123() {
        let mut digits = DigitsIterator::new(123_u32, 10).unwrap();

        assert_eq!(digits.next_back(), Some(3));
        assert_eq!(digits.next_back(), Some(2));
        assert_eq!(digits.next_back(), Some(1));
        assert_eq!(digits.next_back(), None);
    }

    #[test]
    fn test_exact_power() {
        let mut digits = DigitsIterator::new(1000_u32, 10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), Some(0));
        assert_eq!(digits.next(), Some(0));
        assert_eq!(digits.next(), Some(0));
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_reversible_iterator() {
        let mut digits = DigitsIterator::new(123_u32, 10).unwrap().rev();

        assert_eq!(digits.next(), Some(3));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_overflow() {
        let mut digits = DigitsIterator::new(123_u8, 10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next_back(), Some(3));
        assert_eq!(digits.next(), Some(2));
        assert_eq!(digits.next_back(), None);
    }

    #[test]
    fn test_radix_0() {
        let digits = DigitsIterator::new(123_u32, 0);
        assert_eq!(digits, Err(RadixError::Radix0));
    }

    #[test]
    fn test_radix_1() {
        let digits = DigitsIterator::new(123_u32, 1);
        assert_eq!(digits, Err(RadixError::Radix1));
    }

    #[test]
    fn test_len_does_not_consume_iterator() {
        let digits = DigitsIterator::new(123_u32, 10).unwrap();
        assert_eq!(digits.len(), 3);
        assert_eq!(digits.len(), 3);
    }

    #[test]
    fn test_into_number() {
        let number = 123_u8;
        let mut digits = DigitsIterator::new(number, 10).unwrap();
        assert_eq!(number, digits.clone().into_number());
        let _ = digits.next();
        let _ = digits.next_back();
        assert_eq!(2, digits.into_number());
    }

    #[test]
    fn test_into_reversed_number() {
        let number = 255_u8;
        let reversed = DigitsIterator::new(number, 10)
            .unwrap()
            .into_reversed_number();
        assert_ne!(reversed, number);
        assert_eq!(reversed, 40);
    }

    #[test]
    fn test_last() {
        let number = 123_456_u32;
        let mut digits = DigitsIterator::new(number, 10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next_back(), Some(6));
        assert_eq!(digits.last(), Some(5));
    }

    #[test]
    fn test_rotate_left_retains_zeroes() {
        let number = 1023_u32;
        let mut digits = DigitsIterator::new(number, 10).unwrap();
        digits.rotate_left(1);

        assert_eq!(digits.to_number(), 231);
        assert_eq!(digits.next(), Some(0));
    }

    #[test]
    fn test_rotate_right_retains_zeroes() {
        let number = 1230_u32;
        let mut digits = DigitsIterator::new(number, 10).unwrap();
        digits.rotate_right(1);

        assert_eq!(digits.to_number(), 123);
        assert_eq!(digits.next(), Some(0));
    }

    #[test]
    fn test_zero_is_some_then_none() {
        let mut digits = DigitsIterator::new(0_u32, 10).unwrap();

        assert_eq!(digits.next(), Some(0));
        assert_eq!(digits.next(), None);
    }

    #[test]
    fn test_one_is_some_then_none() {
        let mut digits = DigitsIterator::new(1_u32, 10).unwrap();

        assert_eq!(digits.next(), Some(1));
        assert_eq!(digits.next(), None);
    }
}
