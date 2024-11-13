// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`BitInt`] and other types.

use super::BitInt;

macro_rules! impl_from_bit_int_to_underlying_type {
    ($T:ty) => {
        impl<const N: u32> From<BitInt<$T, N>> for $T {
            #[inline]
            fn from(n: BitInt<$T, N>) -> Self {
                n.get()
            }
        }
    };
}
impl_from_bit_int_to_underlying_type!(i8);
impl_from_bit_int_to_underlying_type!(i16);
impl_from_bit_int_to_underlying_type!(i32);
impl_from_bit_int_to_underlying_type!(i64);
impl_from_bit_int_to_underlying_type!(i128);
impl_from_bit_int_to_underlying_type!(isize);

#[cfg(test)]
mod tests {
    use super::super::{BitI128, BitI16, BitI32, BitI64, BitI8};

    #[test]
    fn from_bit_int_to_underlying_type() {
        assert_eq!(i8::from(BitI8::<7>::MAX), i8::MAX >> 1);
        assert_eq!(i16::from(BitI16::<15>::MAX), i16::MAX >> 1);
        assert_eq!(i32::from(BitI32::<31>::MAX), i32::MAX >> 1);
        assert_eq!(i64::from(BitI64::<63>::MAX), i64::MAX >> 1);
        assert_eq!(i128::from(BitI128::<127>::MAX), i128::MAX >> 1);
    }
}
