// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for formatting and printing [`BitUint`].

use core::fmt;

use num_traits::{PrimInt, Unsigned};

use super::BitUint;

macro_rules! impl_fmt {
    ($trait:ident) => {
        impl<T: Unsigned + PrimInt + fmt::$trait, const N: u32> fmt::$trait for BitUint<T, N> {
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
    use super::super::BitU8;

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", BitU8::<7>::MIN), "BitUint(0)");
        assert_eq!(format!("{:?}", BitU8::<7>::MAX), "BitUint(127)");
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", BitU8::<7>::MIN), "0");
        assert_eq!(format!("{}", BitU8::<7>::MAX), "127");
    }

    #[test]
    fn octal() {
        assert_eq!(format!("{:o}", BitU8::<7>::MIN), "0");
        assert_eq!(format!("{:#o}", BitU8::<7>::MAX), "0o177");
    }

    #[test]
    fn lower_hex() {
        assert_eq!(format!("{:x}", BitU8::<7>::MIN), "0");
        assert_eq!(format!("{:#x}", BitU8::<7>::MAX), "0x7f");
    }

    #[test]
    fn upper_hex() {
        assert_eq!(format!("{:X}", BitU8::<7>::MIN), "0");
        assert_eq!(format!("{:#X}", BitU8::<7>::MAX), "0x7F");
    }

    #[test]
    fn binary() {
        assert_eq!(format!("{:b}", BitU8::<7>::MIN), "0");
        assert_eq!(format!("{:#b}", BitU8::<7>::MAX), "0b1111111");
    }

    #[test]
    fn lower_exp() {
        assert_eq!(format!("{:e}", BitU8::<7>::MIN), "0e0");
        assert_eq!(format!("{:e}", BitU8::<7>::MAX), "1.27e2");
    }

    #[test]
    fn upper_exp() {
        assert_eq!(format!("{:E}", BitU8::<7>::MIN), "0E0");
        assert_eq!(format!("{:E}", BitU8::<7>::MAX), "1.27E2");
    }
}
