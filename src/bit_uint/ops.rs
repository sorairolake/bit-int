// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`BitUint`].

use super::BitUint;

macro_rules! impl_ops {
    ($T:ty) => {
        impl<const N: u32> BitUint<$T, N> {
            /// Computes `self + rhs`, returning [`None`] if overflow occurred.
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

            /// Computes `self - rhs`, returning [`None`] if overflow occurred.
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

            /// Computes `self * rhs`, returning [`None`] if overflow occurred.
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

            /// Computes `self / rhs`, returning [`None`] if `rhs == 0`.
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
}
