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
    use super::super::{BitI128, BitI16, BitI32, BitI64, BitI8, BitIsize};

    #[test]
    fn min() {
        assert_eq!(BitI8::<7>::MIN.get(), i8::MIN >> 1);
        assert_eq!(BitI16::<15>::MIN.get(), i16::MIN >> 1);
        assert_eq!(BitI32::<31>::MIN.get(), i32::MIN >> 1);
        assert_eq!(BitI64::<63>::MIN.get(), i64::MIN >> 1);
        assert_eq!(BitI128::<127>::MIN.get(), i128::MIN >> 1);
        assert_eq!(BitIsize::<{ isize::BITS - 1 }>::MIN.get(), isize::MIN >> 1);
    }

    #[test]
    fn min_when_one_bit() {
        assert_eq!(BitI8::<1>::MIN.get(), -1);
        assert_eq!(BitI16::<1>::MIN.get(), -1);
        assert_eq!(BitI32::<1>::MIN.get(), -1);
        assert_eq!(BitI64::<1>::MIN.get(), -1);
        assert_eq!(BitI128::<1>::MIN.get(), -1);
        assert_eq!(BitIsize::<1>::MIN.get(), -1);
    }

    #[test]
    fn min_when_max_bits() {
        assert_eq!(BitI8::<{ i8::BITS }>::MIN.get(), i8::MIN);
        assert_eq!(BitI16::<{ i16::BITS }>::MIN.get(), i16::MIN);
        assert_eq!(BitI32::<{ i32::BITS }>::MIN.get(), i32::MIN);
        assert_eq!(BitI64::<{ i64::BITS }>::MIN.get(), i64::MIN);
        assert_eq!(BitI128::<{ i128::BITS }>::MIN.get(), i128::MIN);
        assert_eq!(BitIsize::<{ isize::BITS }>::MIN.get(), isize::MIN);
    }

    #[test]
    fn max() {
        assert_eq!(BitI8::<7>::MAX.get(), i8::MAX >> 1);
        assert_eq!(BitI16::<15>::MAX.get(), i16::MAX >> 1);
        assert_eq!(BitI32::<31>::MAX.get(), i32::MAX >> 1);
        assert_eq!(BitI64::<63>::MAX.get(), i64::MAX >> 1);
        assert_eq!(BitI128::<127>::MAX.get(), i128::MAX >> 1);
        assert_eq!(BitIsize::<{ isize::BITS - 1 }>::MAX.get(), isize::MAX >> 1);
    }

    #[test]
    fn max_when_one_bit() {
        assert_eq!(BitI8::<1>::MAX.get(), 0);
        assert_eq!(BitI16::<1>::MAX.get(), 0);
        assert_eq!(BitI32::<1>::MAX.get(), 0);
        assert_eq!(BitI64::<1>::MAX.get(), 0);
        assert_eq!(BitI128::<1>::MAX.get(), 0);
        assert_eq!(BitIsize::<1>::MAX.get(), 0);
    }

    #[test]
    fn max_when_max_bits() {
        assert_eq!(BitI8::<{ i8::BITS }>::MAX.get(), i8::MAX);
        assert_eq!(BitI16::<{ i16::BITS }>::MAX.get(), i16::MAX);
        assert_eq!(BitI32::<{ i32::BITS }>::MAX.get(), i32::MAX);
        assert_eq!(BitI64::<{ i64::BITS }>::MAX.get(), i64::MAX);
        assert_eq!(BitI128::<{ i128::BITS }>::MAX.get(), i128::MAX);
        assert_eq!(BitIsize::<{ isize::BITS }>::MAX.get(), isize::MAX);
    }

    #[test]
    fn bits() {
        assert_eq!(BitI8::<7>::BITS, 7);
        assert_eq!(BitI16::<15>::BITS, 15);
        assert_eq!(BitI32::<31>::BITS, 31);
        assert_eq!(BitI64::<63>::BITS, 63);
        assert_eq!(BitI128::<127>::BITS, 127);
        assert_eq!(BitIsize::<{ isize::BITS - 1 }>::BITS, isize::BITS - 1);
    }

    #[test]
    fn bits_when_one_bit() {
        assert_eq!(BitI8::<1>::BITS, 1);
        assert_eq!(BitI16::<1>::BITS, 1);
        assert_eq!(BitI32::<1>::BITS, 1);
        assert_eq!(BitI64::<1>::BITS, 1);
        assert_eq!(BitI128::<1>::BITS, 1);
        assert_eq!(BitIsize::<1>::BITS, 1);
    }

    #[test]
    fn bits_when_max_bits() {
        assert_eq!(BitI8::<{ i8::BITS }>::BITS, i8::BITS);
        assert_eq!(BitI16::<{ i16::BITS }>::BITS, i16::BITS);
        assert_eq!(BitI32::<{ i32::BITS }>::BITS, i32::BITS);
        assert_eq!(BitI64::<{ i64::BITS }>::BITS, i64::BITS);
        assert_eq!(BitI128::<{ i128::BITS }>::BITS, i128::BITS);
        assert_eq!(BitIsize::<{ isize::BITS }>::BITS, isize::BITS);
    }
}
