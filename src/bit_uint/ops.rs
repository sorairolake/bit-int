// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`BitUint`].

use super::BitUint;

macro_rules! impl_ops {
    ($T:ty) => {
        impl<const N: u32> BitUint<$T, N> {
            /// Calculates the addition of `self` and `rhs`.
            ///
            /// Returns [`None`] if overflow occurred.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(42).unwrap();")]
            ///
            /// assert_eq!(n.checked_add(21).map(BitUint::get), Some(63));
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
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(42).unwrap();")]
            ///
            /// assert_eq!(n.checked_sub(42).map(BitUint::get), Some(0));
            /// assert!(n.checked_sub(43).is_none());
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
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(21).unwrap();")]
            ///
            /// assert_eq!(n.checked_mul(2).map(BitUint::get), Some(42));
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
            /// Returns [`None`] if `rhs` is `0`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(42).unwrap();")]
            ///
            /// assert_eq!(n.checked_div(2).map(BitUint::get), Some(21));
            /// assert!(n.checked_div(0).is_none());
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

            /// Calculates the quotient of Euclidean division of `self` by `rhs`.
            ///
            /// Returns [`None`] if `rhs` is `0`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(42).unwrap();")]
            ///
            /// assert_eq!(n.checked_div_euclid(2).map(BitUint::get), Some(21));
            /// assert!(n.checked_div_euclid(0).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_div_euclid(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_div_euclid(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Calculates the remainder when `self` is divided by `rhs`.
            ///
            /// Returns [`None`] if `rhs` is `0`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 3>::new(5).unwrap();")]
            ///
            /// assert_eq!(n.checked_rem(2).map(BitUint::get), Some(1));
            /// assert!(n.checked_rem(0).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_rem(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_rem(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Calculates the multiplication of `self` and `rhs`.
            ///
            /// Returns [`None`] if `rhs` is `0`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 3>::new(5).unwrap();")]
            ///
            /// assert_eq!(n.checked_rem_euclid(2).map(BitUint::get), Some(1));
            /// assert!(n.checked_rem_euclid(0).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_rem_euclid(self, rhs: $T) -> Option<Self> {
                if let Some(result) = self.get().checked_rem_euclid(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Returns the logarithm of the number with respect to an arbitrary base,
            /// rounded down.
            ///
            /// Returns [`None`] if the number is zero, or if the base is not at least
            /// 2.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 3>::new(5).unwrap();")]
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
            /// Returns [`None`] if the number is zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 2>::new(2).unwrap();")]
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
            /// Returns [`None`] if the number is zero.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 4>::new(10).unwrap();")]
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
            /// Returns [`None`] unless `self` is `0`.
            ///
            /// Note that negating any positive integer will overflow.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            /// assert_eq!(
            #[doc = concat!("    BitUint::<", stringify!($T), ", 1>::MIN.checked_neg().map(BitUint::get),")]
            ///     Some(0)
            /// );
            #[doc = concat!("assert!(BitUint::<", stringify!($T), ", 1>::MAX.checked_neg().is_none());")]
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

            /// Shifts `self` left by `rhs` bits.
            ///
            /// Returns [`None`] if `rhs` is larger than or equal to the number of bits
            /// in `self`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 5>::new(0x01).unwrap();")]
            #[doc = concat!("let m = BitUint::<", stringify!($T), ", 5>::new(0x10).unwrap();")]
            ///
            /// assert_eq!(n.checked_shl(4).map(BitUint::get), Some(0x10));
            /// assert!(m.checked_shl(129).is_none());
            #[doc = concat!("assert_eq!(m.checked_shl(", stringify!($T), "::BITS - 1).map(BitUint::get), Some(0x00));")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
                if let Some(result) = self.get().checked_shl(rhs) {
                    Self::new(result)
                } else {
                    None
                }
            }

            /// Shifts `self` right by `rhs` bits.
            ///
            /// Returns [`None`] if `rhs` is larger than or equal to the number of bits
            /// in `self`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 5>::new(0x10).unwrap();")]
            ///
            /// assert_eq!(n.checked_shr(4).map(BitUint::get), Some(0x01));
            /// assert!(n.checked_shr(129).is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
                if let Some(result) = self.get().checked_shr(rhs) {
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
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(2).unwrap();")]
            ///
            /// assert_eq!(n.checked_pow(5).map(BitUint::get), Some(32));
            #[doc = concat!("assert!(BitUint::<", stringify!($T), ", 6>::MAX.checked_pow(2).is_none());")]
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
impl_ops!(u8);
impl_ops!(u16);
impl_ops!(u32);
impl_ops!(u64);
impl_ops!(u128);
impl_ops!(usize);

#[cfg(test)]
mod tests {
    use super::super::BitU8;

    #[test]
    fn checked_add() {
        let n = BitU8::<6>::new(42).unwrap();

        assert_eq!(n.checked_add(21).map(BitU8::get), Some(63));
        assert!(n.checked_add(22).is_none());
    }

    #[test]
    const fn checked_add_is_const_fn() {
        const _: Option<BitU8<6>> = BitU8::<6>::MAX.checked_add(1);
    }

    #[test]
    fn checked_sub() {
        let n = BitU8::<6>::new(42).unwrap();

        assert_eq!(n.checked_sub(42).map(BitU8::get), Some(0));
        assert!(n.checked_sub(43).is_none());
    }

    #[test]
    const fn checked_sub_is_const_fn() {
        const _: Option<BitU8<6>> = BitU8::<6>::MIN.checked_sub(1);
    }

    #[test]
    fn checked_mul() {
        let n = BitU8::<6>::new(21).unwrap();

        assert_eq!(n.checked_mul(2).map(BitU8::get), Some(42));
        assert!(n.checked_mul(4).is_none());
    }

    #[test]
    const fn checked_mul_is_const_fn() {
        const _: Option<BitU8<6>> = BitU8::<6>::MAX.checked_mul(2);
    }

    #[test]
    fn checked_div() {
        let n = BitU8::<6>::new(42).unwrap();

        assert_eq!(n.checked_div(2).map(BitU8::get), Some(21));
        assert!(n.checked_div(0).is_none());
    }

    #[test]
    const fn checked_div_is_const_fn() {
        const _: Option<BitU8<6>> = BitU8::<6>::MAX.checked_div(0);
    }

    #[test]
    fn checked_div_euclid() {
        let n = BitU8::<6>::new(42).unwrap();

        assert_eq!(n.checked_div_euclid(2).map(BitU8::get), Some(21));
        assert!(n.checked_div_euclid(0).is_none());
    }

    #[test]
    const fn checked_div_euclid_is_const_fn() {
        const _: Option<BitU8<6>> = BitU8::<6>::MAX.checked_div_euclid(0);
    }

    #[test]
    fn checked_rem() {
        let n = BitU8::<3>::new(5).unwrap();

        assert_eq!(n.checked_rem(2).map(BitU8::get), Some(1));
        assert!(n.checked_rem(0).is_none());
    }

    #[test]
    const fn checked_rem_is_const_fn() {
        const _: Option<BitU8<3>> = BitU8::<3>::MAX.checked_rem(0);
    }

    #[test]
    fn checked_rem_euclid() {
        let n = BitU8::<3>::new(5).unwrap();

        assert_eq!(n.checked_rem_euclid(2).map(BitU8::get), Some(1));
        assert!(n.checked_rem_euclid(0).is_none());
    }

    #[test]
    const fn checked_rem_euclid_is_const_fn() {
        const _: Option<BitU8<3>> = BitU8::<3>::MAX.checked_rem_euclid(0);
    }

    #[test]
    fn checked_ilog() {
        let n = BitU8::<3>::new(5).unwrap();

        assert_eq!(n.checked_ilog(5), Some(1));
        assert!(n.checked_ilog(1).is_none());
        assert!(BitU8::<3>::MIN.checked_ilog(5).is_none());
    }

    #[test]
    const fn checked_ilog_is_const_fn() {
        const _: Option<u32> = BitU8::<3>::MIN.checked_ilog(5);
    }

    #[test]
    fn checked_ilog2() {
        let n = BitU8::<2>::new(2).unwrap();

        assert_eq!(n.checked_ilog2(), Some(1));
        assert!(BitU8::<2>::MIN.checked_ilog2().is_none());
    }

    #[test]
    const fn checked_ilog2_is_const_fn() {
        const _: Option<u32> = BitU8::<2>::MIN.checked_ilog2();
    }

    #[test]
    fn checked_ilog10() {
        let n = BitU8::<4>::new(10).unwrap();

        assert_eq!(n.checked_ilog10(), Some(1));
        assert!(BitU8::<4>::MIN.checked_ilog10().is_none());
    }

    #[test]
    const fn checked_ilog10_is_const_fn() {
        const _: Option<u32> = BitU8::<4>::MIN.checked_ilog10();
    }

    #[test]
    fn checked_neg() {
        assert_eq!(BitU8::<1>::MIN.checked_neg().map(BitU8::get), Some(0));
        assert!(BitU8::<1>::MAX.checked_neg().is_none());
    }

    #[test]
    const fn checked_neg_is_const_fn() {
        const _: Option<BitU8<1>> = BitU8::<1>::MAX.checked_neg();
    }

    #[test]
    fn checked_shl() {
        let n = BitU8::<5>::new(0x01).unwrap();
        let m = BitU8::<5>::new(0x10).unwrap();

        assert_eq!(n.checked_shl(4).map(BitU8::get), Some(0x10));
        assert!(m.checked_shl(129).is_none());
        assert_eq!(m.checked_shl(u8::BITS - 1).map(BitU8::get), Some(0x00));
    }

    #[test]
    const fn checked_shl_is_const_fn() {
        const _: Option<BitU8<5>> = BitU8::<5>::MIN.checked_shl(129);
    }

    #[test]
    fn checked_shr() {
        let n = BitU8::<5>::new(0x10).unwrap();

        assert_eq!(n.checked_shr(4).map(BitU8::get), Some(0x01));
        assert!(n.checked_shr(129).is_none());
    }

    #[test]
    const fn checked_shr_is_const_fn() {
        const _: Option<BitU8<5>> = BitU8::<5>::MIN.checked_shr(129);
    }

    #[test]
    fn checked_pow() {
        let n = BitU8::<6>::new(2).unwrap();

        assert_eq!(n.checked_pow(5).map(BitU8::get), Some(32));
        assert!(BitU8::<6>::MAX.checked_pow(2).is_none());
    }

    #[test]
    const fn checked_pow_is_const_fn() {
        const _: Option<BitU8<6>> = BitU8::<6>::MAX.checked_pow(2);
    }
}
