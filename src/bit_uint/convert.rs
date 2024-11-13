// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementations of conversions between [`BitUint`] and other types.

use super::BitUint;

macro_rules! impl_from_bit_uint_to_underlying_type {
    ($T:ty) => {
        impl<const N: u32> From<BitUint<$T, N>> for $T {
            #[inline]
            fn from(n: BitUint<$T, N>) -> Self {
                n.get()
            }
        }
    };
}
impl_from_bit_uint_to_underlying_type!(u8);
impl_from_bit_uint_to_underlying_type!(u16);
impl_from_bit_uint_to_underlying_type!(u32);
impl_from_bit_uint_to_underlying_type!(u64);
impl_from_bit_uint_to_underlying_type!(u128);
impl_from_bit_uint_to_underlying_type!(usize);

#[cfg(test)]
mod tests {
    use super::super::{BitU128, BitU16, BitU32, BitU64, BitU8};

    #[test]
    fn from_bit_uint_to_underlying_type() {
        assert_eq!(u8::from(BitU8::<7>::MAX), u8::MAX >> 1);
        assert_eq!(u16::from(BitU16::<15>::MAX), u16::MAX >> 1);
        assert_eq!(u32::from(BitU32::<31>::MAX), u32::MAX >> 1);
        assert_eq!(u64::from(BitU64::<63>::MAX), u64::MAX >> 1);
        assert_eq!(u128::from(BitU128::<127>::MAX), u128::MAX >> 1);
    }
}
