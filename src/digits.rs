use crate::traits::UnsignedInteger;

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
/// use radixal::digits::DigitsIterator;
///
/// let mut digits = DigitsIterator::new(123_u32, 10).expect("Bad radix.");
///
/// assert_eq!(digits.next(), Some(1));
/// assert_eq!(digits.next(), Some(2));
/// assert_eq!(digits.next(), Some(3));
/// assert_eq!(digits.next(), None);
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigitsIterator<T: UnsignedInteger> {
    current: T,
    radix: T,
    splitter: T,
    len: usize,
}

impl<T: UnsignedInteger> DigitsIterator<T> {
    /// Create a new `DigitsIterator` for `number` using `radix`.
    ///
    /// Returns an `Err(RadixError)` if the radix is `0` is `1`.
    pub fn new(number: T, radix: T) -> Result<DigitsIterator<T>, RadixError> {
        if radix == T::ZERO {
            return Err(RadixError::Radix0);
        } else if radix == T::ONE {
            return Err(RadixError::Radix1);
        }

        let mut len = 1;
        let mut splitter = T::ONE;
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
}

impl<T: UnsignedInteger> Iterator for DigitsIterator<T> {
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

impl<T: UnsignedInteger> DoubleEndedIterator for DigitsIterator<T> {
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

impl<T: UnsignedInteger> core::iter::FusedIterator for DigitsIterator<T> {}

impl<T: UnsignedInteger> ExactSizeIterator for DigitsIterator<T> {}

#[cfg(test)]
mod tests {
    use super::*;

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
}
