// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`BitInt`].

use super::BitInt;

macro_rules! impl_ops {
    ($T:ty) => {
        impl<const N: u32> BitInt<$T, N> {
            /// Calculates the addition of `self` and `rhs`.
            ///
            /// Returns [`None`] if overflow occurred.
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

            /// Calculates the subtraction of `rhs` from `self`.
            ///
            /// Returns [`None`] if overflow occurred.
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

            /// Calculates the multiplication of `self` and `rhs`.
            ///
            /// Returns [`None`] if overflow occurred.
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

            /// Calculates the divisor when `self` is divided by `rhs`.
            ///
            /// Returns [`None`] if `rhs` is `0` or the division results in overflow.
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

            /// Calculates the remainder when `self` is divided by `rhs`.
            ///
            /// Returns [`None`] if `rhs` is `0` or the division results in overflow.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 4>::new(5).unwrap();")]
            ///
            /// assert_eq!(n.checked_rem(2).map(BitInt::get), Some(1));
            /// assert!(n.checked_rem(0).is_none());
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 4>::MIN.checked_rem(-1).is_none());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_rem(self, rhs: $T) -> Option<Self> {
                match self.get().checked_rem(rhs) {
                    Some(result) if self.checked_div(rhs).is_some() => Self::new(result),
                    _ => None,
                }
            }

            /// Returns the logarithm of the number with respect to an arbitrary base,
            /// rounded down.
            ///
            /// Returns [`None`] if the number is negative or zero, or if the base is
            /// not at least 2.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 4>::new(5).unwrap();")]
            ///
            /// assert_eq!(n.checked_ilog(5), Some(1));
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_ilog(self, base: $T) -> Option<u32> {
                self.get().checked_ilog(base)
            }

            /// Returns the base 2 logarithm of the number, rounded down.
            ///
            /// Returns [`None`] if the number is negative or zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 3>::new(2).unwrap();")]
            ///
            /// assert_eq!(n.checked_ilog2(), Some(1));
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_ilog2(self) -> Option<u32> {
                self.get().checked_ilog2()
            }

            /// Returns the base 10 logarithm of the number, rounded down.
            ///
            /// Returns [`None`] if the number is negative or zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 5>::new(10).unwrap();")]
            ///
            /// assert_eq!(n.checked_ilog10(), Some(1));
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_ilog10(self) -> Option<u32> {
                self.get().checked_ilog10()
            }

            /// Negates `self`.
            ///
            /// Returns [`None`] if `self` is [`Self::MIN`].
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 4>::new(5).unwrap();")]
            ///
            /// assert_eq!(n.checked_neg().map(BitInt::get), Some(-5));
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 4>::MIN.checked_neg().is_none());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_neg(self) -> Option<Self> {
                if let Some(result) = self.get().checked_neg() {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Computes the absolute value of `self`.
            ///
            /// Returns [`None`] if `self` is [`Self::MIN`].
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 4>::new(-5).unwrap();")]
            ///
            /// assert_eq!(n.checked_abs().map(BitInt::get), Some(5));
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 4>::MIN.checked_abs().is_none());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_abs(self) -> Option<Self> {
                if let Some(result) = self.get().checked_abs() {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Raises `self` to the power of `exp`, using exponentiation by squaring.
            ///
            /// Returns [`None`] if overflow occurred.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 8>::new(8).unwrap();")]
            ///
            /// assert_eq!(n.checked_pow(2).map(BitInt::get), Some(64));
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 8>::MAX.checked_pow(2).is_none());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_pow(self, exp: u32) -> Option<Self> {
                if let Some(result) = self.get().checked_pow(exp) {
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
    const fn checked_add_is_const_fn() {
        const _: Option<BitI8<7>> = BitI8::<7>::MAX.checked_add(1);
    }

    #[test]
    fn checked_sub() {
        let n = BitI8::<7>::new(-42).unwrap();

        assert_eq!(n.checked_sub(22).map(BitI8::get), Some(-64));
        assert!(n.checked_sub(23).is_none());
    }

    #[test]
    const fn checked_sub_is_const_fn() {
        const _: Option<BitI8<7>> = BitI8::<7>::MIN.checked_sub(1);
    }

    #[test]
    fn checked_mul() {
        let n = BitI8::<7>::new(21).unwrap();

        assert_eq!(n.checked_mul(2).map(BitI8::get), Some(42));
        assert!(n.checked_mul(4).is_none());
    }

    #[test]
    const fn checked_mul_is_const_fn() {
        const _: Option<BitI8<7>> = BitI8::<7>::MAX.checked_mul(2);
    }

    #[test]
    fn checked_div() {
        let n = BitI8::<7>::new(42).unwrap();

        assert_eq!(n.checked_div(2).map(BitI8::get), Some(21));
        assert!(n.checked_div(0).is_none());
        assert!(BitI8::<7>::MIN.checked_div(-1).is_none());
    }

    #[test]
    const fn checked_div_is_const_fn() {
        const _: Option<BitI8<7>> = BitI8::<7>::MAX.checked_div(0);
    }

    #[test]
    fn checked_rem() {
        let n = BitI8::<4>::new(5).unwrap();

        assert_eq!(n.checked_rem(2).map(BitI8::get), Some(1));
        assert!(n.checked_rem(0).is_none());
        assert!(BitI8::<4>::MIN.checked_rem(-1).is_none());
    }

    #[test]
    const fn checked_rem_is_const_fn() {
        const _: Option<BitI8<4>> = BitI8::<4>::MAX.checked_rem(0);
    }

    #[test]
    fn checked_ilog() {
        let n = BitI8::<4>::new(5).unwrap();

        assert_eq!(n.checked_ilog(5), Some(1));
        assert!(n.checked_ilog(1).is_none());
        assert!(BitI8::<4>::MIN.checked_ilog(5).is_none());
    }

    #[test]
    const fn checked_ilog_is_const_fn() {
        const _: Option<u32> = BitI8::<4>::MIN.checked_ilog(5);
    }

    #[test]
    fn checked_ilog2() {
        let n = BitI8::<3>::new(2).unwrap();

        assert_eq!(n.checked_ilog2(), Some(1));
        assert!(BitI8::<3>::MIN.checked_ilog2().is_none());
    }

    #[test]
    const fn checked_ilog2_is_const_fn() {
        const _: Option<u32> = BitI8::<3>::MIN.checked_ilog2();
    }

    #[test]
    fn checked_ilog10() {
        let n = BitI8::<5>::new(10).unwrap();

        assert_eq!(n.checked_ilog10(), Some(1));
        assert!(BitI8::<5>::MIN.checked_ilog10().is_none());
    }

    #[test]
    const fn checked_ilog10_is_const_fn() {
        const _: Option<u32> = BitI8::<5>::MIN.checked_ilog10();
    }

    #[test]
    fn checked_neg() {
        let n = BitI8::<4>::new(5).unwrap();

        assert_eq!(n.checked_neg().map(BitI8::get), Some(-5));
        assert!(BitI8::<4>::MIN.checked_neg().is_none());
    }

    #[test]
    const fn checked_neg_is_const_fn() {
        const _: Option<BitI8<4>> = BitI8::<4>::MIN.checked_neg();
    }

    #[test]
    fn checked_abs() {
        let n = BitI8::<4>::new(-5).unwrap();

        assert_eq!(n.checked_abs().map(BitI8::get), Some(5));
        assert!(BitI8::<4>::MIN.checked_abs().is_none());
    }

    #[test]
    const fn checked_abs_is_const_fn() {
        const _: Option<BitI8<4>> = BitI8::<4>::MIN.checked_abs();
    }

    #[test]
    fn checked_pow() {
        let n = BitI8::<8>::new(8).unwrap();

        assert_eq!(n.checked_pow(2).map(BitI8::get), Some(64));
        assert!(BitI8::<8>::MAX.checked_pow(2).is_none());
    }

    #[test]
    const fn checked_pow_is_const_fn() {
        const _: Option<BitI8<8>> = BitI8::<8>::MAX.checked_pow(2);
    }
}
