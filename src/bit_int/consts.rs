// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`BitInt`].

use super::BitInt;

macro_rules! impl_consts {
    ($T:ty) => {
        impl<const N: u32> BitInt<$T, N> {
            /// The smallest value that can be represented by this `BitInt`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("assert_eq!(BitInt::<", stringify!($T), ", 7>::MIN.get(), -64);")]
            /// ```
            // SAFETY: because `MIN` must be the smallest value of a `N`-bit signed integer.
            pub const MIN: Self =
                unsafe { Self::new_unchecked(<$T>::MIN >> (<$T>::BITS - Self::BITS)) };

            /// The largest value that can be represented by this `BitInt`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("assert_eq!(BitInt::<", stringify!($T), ", 7>::MAX.get(), 63);")]
            /// ```
            // SAFETY: because `MAX` must be the largest value of a `N`-bit signed integer.
            pub const MAX: Self =
                unsafe { Self::new_unchecked(<$T>::MAX >> (<$T>::BITS - Self::BITS)) };

            /// The size of this `BitInt` in bits.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("assert_eq!(BitInt::<", stringify!($T), ", 7>::BITS, 7);")]
            /// ```
            pub const BITS: u32 = N;
        }
    };
}
impl_consts!(i8);
impl_consts!(i16);
impl_consts!(i32);
impl_consts!(i64);
impl_consts!(i128);
impl_consts!(isize);

#[cfg(test)]
mod tests {
    use super::super::{BitI128, BitI16, BitI32, BitI64, BitI8};

    #[test]
    fn min() {
        assert_eq!(BitI8::<7>::MIN.get(), i8::MIN >> 1);
        assert_eq!(BitI16::<15>::MIN.get(), i16::MIN >> 1);
        assert_eq!(BitI32::<31>::MIN.get(), i32::MIN >> 1);
        assert_eq!(BitI64::<63>::MIN.get(), i64::MIN >> 1);
        assert_eq!(BitI128::<127>::MIN.get(), i128::MIN >> 1);
    }

    #[test]
    fn max() {
        assert_eq!(BitI8::<7>::MAX.get(), i8::MAX >> 1);
        assert_eq!(BitI16::<15>::MAX.get(), i16::MAX >> 1);
        assert_eq!(BitI32::<31>::MAX.get(), i32::MAX >> 1);
        assert_eq!(BitI64::<63>::MAX.get(), i64::MAX >> 1);
        assert_eq!(BitI128::<127>::MAX.get(), i128::MAX >> 1);
    }

    #[test]
    fn bits() {
        assert_eq!(BitI8::<7>::BITS, 7);
        assert_eq!(BitI16::<15>::BITS, 15);
        assert_eq!(BitI32::<31>::BITS, 31);
        assert_eq!(BitI64::<63>::BITS, 63);
        assert_eq!(BitI128::<127>::BITS, 127);
    }
}
