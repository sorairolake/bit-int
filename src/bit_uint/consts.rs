// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constants for [`BitUint`].

use super::BitUint;

macro_rules! impl_consts {
    ($T:ty) => {
        impl<const N: u32> BitUint<$T, N> {
            /// The smallest value that can be represented by this `BitUint`.
            ///
            /// The value is always `0`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("assert_eq!(BitUint::<", stringify!($T), ", 7>::MIN.get(), 0);")]
            /// ```
            // SAFETY: because `MIN` must be the smallest value of a `N`-bit unsigned
            // integer.
            pub const MIN: Self = unsafe { Self::new_unchecked(<$T>::MIN) };

            /// The largest value that can be represented by this `BitUint`.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("assert_eq!(BitUint::<", stringify!($T), ", 7>::MAX.get(), 127);")]
            /// ```
            // SAFETY: because `MAX` must be the largest value of a `N`-bit unsigned
            // integer.
            pub const MAX: Self =
                unsafe { Self::new_unchecked(<$T>::MAX >> (<$T>::BITS - Self::BITS)) };

            /// The size of this `BitUint` in bits.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("assert_eq!(BitUint::<", stringify!($T), ", 7>::BITS, 7);")]
            /// ```
            pub const BITS: u32 = N;
        }
    };
}
impl_consts!(u8);
impl_consts!(u16);
impl_consts!(u32);
impl_consts!(u64);
impl_consts!(u128);
impl_consts!(usize);

#[cfg(test)]
mod tests {
    use super::super::{BitU8, BitU16, BitU32, BitU64, BitU128, BitUsize};

    #[test]
    fn min() {
        assert_eq!(BitU8::<7>::MIN.get(), u8::MIN);
        assert_eq!(BitU16::<15>::MIN.get(), u16::MIN);
        assert_eq!(BitU32::<31>::MIN.get(), u32::MIN);
        assert_eq!(BitU64::<63>::MIN.get(), u64::MIN);
        assert_eq!(BitU128::<127>::MIN.get(), u128::MIN);
        assert_eq!(BitUsize::<{ usize::BITS - 1 }>::MIN.get(), usize::MIN);
    }

    #[test]
    fn min_when_one_bit() {
        assert_eq!(BitU8::<1>::MIN.get(), u8::MIN);
        assert_eq!(BitU16::<1>::MIN.get(), u16::MIN);
        assert_eq!(BitU32::<1>::MIN.get(), u32::MIN);
        assert_eq!(BitU64::<1>::MIN.get(), u64::MIN);
        assert_eq!(BitU128::<1>::MIN.get(), u128::MIN);
        assert_eq!(BitUsize::<1>::MIN.get(), usize::MIN);
    }

    #[test]
    fn min_when_max_bits() {
        assert_eq!(BitU8::<{ u8::BITS }>::MIN.get(), u8::MIN);
        assert_eq!(BitU16::<{ u16::BITS }>::MIN.get(), u16::MIN);
        assert_eq!(BitU32::<{ u32::BITS }>::MIN.get(), u32::MIN);
        assert_eq!(BitU64::<{ u64::BITS }>::MIN.get(), u64::MIN);
        assert_eq!(BitU128::<{ u128::BITS }>::MIN.get(), u128::MIN);
        assert_eq!(BitUsize::<{ usize::BITS }>::MIN.get(), usize::MIN);
    }

    #[test]
    fn max() {
        assert_eq!(BitU8::<7>::MAX.get(), u8::MAX >> 1);
        assert_eq!(BitU16::<15>::MAX.get(), u16::MAX >> 1);
        assert_eq!(BitU32::<31>::MAX.get(), u32::MAX >> 1);
        assert_eq!(BitU64::<63>::MAX.get(), u64::MAX >> 1);
        assert_eq!(BitU128::<127>::MAX.get(), u128::MAX >> 1);
        assert_eq!(BitUsize::<{ usize::BITS - 1 }>::MAX.get(), usize::MAX >> 1);
    }

    #[test]
    fn max_when_one_bit() {
        assert_eq!(BitU8::<1>::MAX.get(), 1);
        assert_eq!(BitU16::<1>::MAX.get(), 1);
        assert_eq!(BitU32::<1>::MAX.get(), 1);
        assert_eq!(BitU64::<1>::MAX.get(), 1);
        assert_eq!(BitU128::<1>::MAX.get(), 1);
        assert_eq!(BitUsize::<1>::MAX.get(), 1);
    }

    #[test]
    fn max_when_max_bits() {
        assert_eq!(BitU8::<{ u8::BITS }>::MAX.get(), u8::MAX);
        assert_eq!(BitU16::<{ u16::BITS }>::MAX.get(), u16::MAX);
        assert_eq!(BitU32::<{ u32::BITS }>::MAX.get(), u32::MAX);
        assert_eq!(BitU64::<{ u64::BITS }>::MAX.get(), u64::MAX);
        assert_eq!(BitU128::<{ u128::BITS }>::MAX.get(), u128::MAX);
        assert_eq!(BitUsize::<{ usize::BITS }>::MAX.get(), usize::MAX);
    }

    #[test]
    fn bits() {
        assert_eq!(BitU8::<7>::BITS, 7);
        assert_eq!(BitU16::<15>::BITS, 15);
        assert_eq!(BitU32::<31>::BITS, 31);
        assert_eq!(BitU64::<63>::BITS, 63);
        assert_eq!(BitU128::<127>::BITS, 127);
        assert_eq!(BitUsize::<{ usize::BITS - 1 }>::BITS, usize::BITS - 1);
    }

    #[test]
    fn bits_when_one_bit() {
        assert_eq!(BitU8::<1>::BITS, 1);
        assert_eq!(BitU16::<1>::BITS, 1);
        assert_eq!(BitU32::<1>::BITS, 1);
        assert_eq!(BitU64::<1>::BITS, 1);
        assert_eq!(BitU128::<1>::BITS, 1);
        assert_eq!(BitUsize::<1>::BITS, 1);
    }

    #[test]
    fn bits_when_max_bits() {
        assert_eq!(BitU8::<{ u8::BITS }>::BITS, u8::BITS);
        assert_eq!(BitU16::<{ u16::BITS }>::BITS, u16::BITS);
        assert_eq!(BitU32::<{ u32::BITS }>::BITS, u32::BITS);
        assert_eq!(BitU64::<{ u64::BITS }>::BITS, u64::BITS);
        assert_eq!(BitU128::<{ u128::BITS }>::BITS, u128::BITS);
        assert_eq!(BitUsize::<{ usize::BITS }>::BITS, usize::BITS);
    }
}
