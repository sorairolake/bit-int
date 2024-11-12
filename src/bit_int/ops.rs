// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`BitInt`].

use super::BitInt;

macro_rules! impl_ops {
    ($T:ty) => {
        impl<const N: u32> BitInt<$T, N> {
            /// Computes `self + rhs`, returning [`None`] if overflow occurred.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 7>::new(42).unwrap();")]
            ///
            /// assert_eq!(n.checked_add(21).map(BitInt::get), Some(63));
            /// assert!(n.checked_add(22).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_add(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_add(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Computes `self - rhs`, returning [`None`] if overflow occurred.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 7>::new(-42).unwrap();")]
            ///
            /// assert_eq!(n.checked_sub(22).map(BitInt::get), Some(-64));
            /// assert!(n.checked_sub(23).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_sub(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_sub(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Computes `self * rhs`, returning [`None`] if overflow occurred.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 7>::new(21).unwrap();")]
            ///
            /// assert_eq!(n.checked_mul(2).map(BitInt::get), Some(42));
            /// assert!(n.checked_mul(4).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_mul(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_mul(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Computes `self / rhs`, returning [`None`] if `rhs == 0` or the division
            /// results in overflow.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 7>::new(42).unwrap();")]
            ///
            /// assert_eq!(n.checked_div(2).map(BitInt::get), Some(21));
            /// assert!(n.checked_div(0).is_none());
            ///
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 7>::MIN.checked_div(-1).is_none());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_div(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_div(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }
        }
    };
}
impl_ops!(i8);
impl_ops!(i16);
impl_ops!(i32);
impl_ops!(i64);
impl_ops!(i128);
impl_ops!(isize);

#[cfg(test)]
mod tests {
    use super::super::BitI8;

    #[test]
    fn checked_add() {
        let n = BitI8::<7>::new(42).unwrap();

        assert_eq!(n.checked_add(21).map(BitI8::get), Some(63));
        assert!(n.checked_add(22).is_none());
    }

    #[test]
    fn checked_sub() {
        let n = BitI8::<7>::new(-42).unwrap();

        assert_eq!(n.checked_sub(22).map(BitI8::get), Some(-64));
        assert!(n.checked_sub(23).is_none());
    }

    #[test]
    fn checked_mul() {
        let n = BitI8::<7>::new(21).unwrap();

        assert_eq!(n.checked_mul(2).map(BitI8::get), Some(42));
        assert!(n.checked_mul(4).is_none());
    }

    #[test]
    fn checked_div() {
        let n = BitI8::<7>::new(42).unwrap();

        assert_eq!(n.checked_div(2).map(BitI8::get), Some(21));
        assert!(n.checked_div(0).is_none());

        assert!(BitI8::<7>::MIN.checked_div(-1).is_none());
    }
}
