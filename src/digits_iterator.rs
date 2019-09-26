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
/// ```
/// use radixal::digits_iterator::DigitsIterator;
///
/// let mut digits = DigitsIterator::new(123_u32, 10).expect("Bad radix.");
///
/// assert_eq!(digits.next(), Some(1));
/// assert_eq!(digits.next(), Some(2));
/// assert_eq!(digits.next(), Some(3));
/// assert_eq!(digits.next(), None);
/// ```
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
    pub fn new(number: T, radix: T) -> Result<DigitsIterator<T>, RadixError> {
        if radix == T::zero() {
            return Err(RadixError::Radix0);
        } else if radix == T::one() {
            return Err(RadixError::Radix1);
        }

        let mut len = 1;
        let mut splitter = T::one();
        let mut n = number;

        while n >= radix {
            len += 1;
            splitter = splitter * radix;
            n = n / radix;
        }

        Ok(DigitsIterator {
            current: number,
            radix,
            splitter,
            len,
        })
    }

    /// Checks whether the number is a palindrome.
    #[allow(clippy::wrong_self_convention)]
    pub fn is_palindrome(mut self) -> bool {
        while self.len > 1 {
            if self.next() != self.next_back() {
                return false;
            }
        }

        true
    }

    /// Converts the DigitsIterator into a number.
    pub fn into_number(self) -> T {
        let radix = self.radix;
        self.fold(T::zero(), |acc, digit| acc * radix + digit)
    }

    /// Converts the DigitsIterator into a number with the digits reversed, using wrapping
    /// semantics if necessary.
    pub fn into_reversed_number(self) -> T {
        let radix = self.radix;
        self.rfold(T::zero(), |acc, digit| {
            acc.wrapping_mul(&radix).wrapping_add(&digit)
        })
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

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    // TODO: Provide a better implementation for `nth` and `step_by`.
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

    // TODO: Provide a better implementation for `nth_back`.
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
        let digits = DigitsIterator::new(number, 10).unwrap();
        assert_eq!(number, digits.into_number());
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
}
