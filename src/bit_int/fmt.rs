// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for formatting and printing [`BitInt`].

use core::fmt;

use num_traits::{PrimInt, Signed};

use super::BitInt;

macro_rules! impl_fmt {
    ($trait:ident) => {
        impl<T: Signed + PrimInt + fmt::$trait, const N: u32> fmt::$trait for BitInt<T, N> {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.get().fmt(f)
            }
        }
    };
}
impl_fmt!(Display);
impl_fmt!(Octal);
impl_fmt!(LowerHex);
impl_fmt!(UpperHex);
impl_fmt!(Binary);
impl_fmt!(LowerExp);
impl_fmt!(UpperExp);

#[cfg(test)]
mod tests {
    use super::super::BitI8;

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", BitI8::<7>::MIN), "BitInt(-64)");
        assert_eq!(format!("{:?}", BitI8::<7>::MAX), "BitInt(63)");
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", BitI8::<7>::MIN), "-64");
        assert_eq!(format!("{}", BitI8::<7>::MAX), "63");
    }

    #[test]
    fn octal() {
        assert_eq!(format!("{:o}", BitI8::<7>::MIN), "300");
        assert_eq!(format!("{:#o}", BitI8::<7>::MAX), "0o77");
    }

    #[test]
    fn lower_hex() {
        assert_eq!(format!("{:x}", BitI8::<7>::MIN), "c0");
        assert_eq!(format!("{:#x}", BitI8::<7>::MAX), "0x3f");
    }

    #[test]
    fn upper_hex() {
        assert_eq!(format!("{:X}", BitI8::<7>::MIN), "C0");
        assert_eq!(format!("{:#X}", BitI8::<7>::MAX), "0x3F");
    }

    #[test]
    fn binary() {
        assert_eq!(format!("{:b}", BitI8::<7>::MIN), "11000000");
        assert_eq!(format!("{:#b}", BitI8::<7>::MAX), "0b111111");
    }

    #[test]
    fn lower_exp() {
        assert_eq!(format!("{:e}", BitI8::<7>::MIN), "-6.4e1");
        assert_eq!(format!("{:e}", BitI8::<7>::MAX), "6.3e1");
    }

    #[test]
    fn upper_exp() {
        assert_eq!(format!("{:E}", BitI8::<7>::MIN), "-6.4E1");
        assert_eq!(format!("{:E}", BitI8::<7>::MAX), "6.3E1");
    }
}
