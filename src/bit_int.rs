// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An arbitrary fixed bit-width signed integer.

mod cmp;
mod consts;
mod fmt;
mod ops;

use num_traits::{PrimInt, Signed};

/// `BitInt` is a type that represents a `N`-bit signed integer.
///
/// The largest size of `N` is equal to the size of the underlying type in bits.
///
/// # Examples
///
/// ```compile_fail
/// use bit_int::BitInt;
///
/// let n = BitInt::<i32, 33>::new(42);
/// assert_eq!(n.map(BitInt::get), Some(42));
/// ```
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitInt<T: Signed + PrimInt, const N: u32>(T);

macro_rules! impl_bit_int {
    ($T:ty, $alias:ident) => {
        impl<const N: u32> BitInt<$T, N> {
            /// Creates a new `BitInt` with the given signed integer value.
            ///
            /// Returns [`None`] if the value is not a valid `N`-bit signed integer.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("let n = BitInt::<", stringify!($T), ", 7>::new(42);")]
            /// assert_eq!(n.map(BitInt::get), Some(42));
            #[doc = ""]
            #[doc = concat!("let m = BitInt::<", stringify!($T), ", 6>::new(42);")]
            /// assert!(m.is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn new(n: $T) -> Option<Self> {
                if n >= Self::MIN.get() && n <= Self::MAX.get() {
                    // SAFETY: `n` is checked to be a valid `N`-bit signed integer.
                    let n = unsafe { Self::new_unchecked(n) };
                    Some(n)
                } else {
                    None
                }
            }

            /// Returns [`true`] if `self` is positive and [`false`] if the number is
            /// zero or negative.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("assert!(!BitInt::<", stringify!($T), ", 7>::MIN.is_positive());")]
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 7>::MAX.is_positive());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn is_positive(self) -> bool {
                self.get().is_positive()
            }

            /// Returns [`true`] if `self` is negative and [`false`] if the number is
            /// zero or positive.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitInt;
            /// #
            #[doc = concat!("assert!(BitInt::<", stringify!($T), ", 7>::MIN.is_negative());")]
            #[doc = concat!("assert!(!BitInt::<", stringify!($T), ", 7>::MAX.is_negative());")]
            /// ```
            #[must_use]
            #[inline]
            pub const fn is_negative(self) -> bool {
                self.get().is_negative()
            }
        }

        /// A specialized [`BitInt`] type whose the underlying type is restricted to
        #[doc = concat!("[`", stringify!($T), "`].")]
        ///
        #[doc = concat!("The largest size of `N` is equal to [`", stringify!($T), "::BITS`].")]
        pub type $alias<const N: u32> = BitInt<$T, N>;
    };
}
impl_bit_int!(i8, BitI8);
impl_bit_int!(i16, BitI16);
impl_bit_int!(i32, BitI32);
impl_bit_int!(i64, BitI64);
impl_bit_int!(i128, BitI128);
impl_bit_int!(isize, BitIsize);

impl<T: Signed + PrimInt, const N: u32> BitInt<T, N> {
    /// Creates a new `BitInt` with the given signed integer value.
    ///
    /// This method does not check whether the value is a valid `N`-bit signed
    /// integer. This results in undefined behaviour if the value is not a valid
    /// `N`-bit signed integer.
    ///
    /// # Safety
    ///
    /// The value must be a valid `N`-bit signed integer.
    #[must_use]
    #[inline]
    pub const unsafe fn new_unchecked(n: T) -> Self {
        Self(n)
    }

    /// Returns the contained value as the underlying type.
    #[must_use]
    #[inline]
    pub const fn get(self) -> T {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use core::{any, mem};

    use super::*;

    #[test]
    fn alias() {
        assert_eq!(
            any::type_name::<BitI8::<7>>(),
            any::type_name::<BitInt::<i8, 7>>()
        );
        assert_eq!(
            any::type_name::<BitI16::<15>>(),
            any::type_name::<BitInt::<i16, 15>>()
        );
        assert_eq!(
            any::type_name::<BitI32::<31>>(),
            any::type_name::<BitInt::<i32, 31>>()
        );
        assert_eq!(
            any::type_name::<BitI64::<63>>(),
            any::type_name::<BitInt::<i64, 63>>()
        );
        assert_eq!(
            any::type_name::<BitI128::<127>>(),
            any::type_name::<BitInt::<i128, 127>>()
        );
        assert_eq!(
            any::type_name::<BitIsize::<31>>(),
            any::type_name::<BitInt::<isize, 31>>()
        );
    }

    #[test]
    fn layout() {
        assert_eq!(mem::size_of::<BitI32::<31>>(), mem::size_of::<i32>());
        assert_eq!(mem::align_of::<BitI32::<31>>(), mem::align_of::<i32>());
    }

    #[test]
    fn clone() {
        assert_eq!(BitI32::<31>::MIN.clone(), BitI32::<31>::MIN);
    }

    #[test]
    fn copy() {
        let a = BitI32::<31>::MIN;
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn default() {
        assert_eq!(
            BitI32::<31>::default(),
            BitI32::<31>::new(i32::default()).unwrap()
        );
    }

    #[test]
    fn new() {
        assert_eq!(
            BitI8::<7>::new(i8::MAX >> 1).map(BitI8::get),
            Some(i8::MAX >> 1)
        );
        assert_eq!(
            BitI16::<15>::new(i16::MAX >> 1).map(BitI16::get),
            Some(i16::MAX >> 1)
        );
        assert_eq!(
            BitI32::<31>::new(i32::MAX >> 1).map(BitI32::get),
            Some(i32::MAX >> 1)
        );
        assert_eq!(
            BitI64::<63>::new(i64::MAX >> 1).map(BitI64::get),
            Some(i64::MAX >> 1)
        );
        assert_eq!(
            BitI128::<127>::new(i128::MAX >> 1).map(BitI128::get),
            Some(i128::MAX >> 1)
        );
    }

    #[test]
    fn new_with_invalid_value() {
        assert!(BitI8::<7>::new((i8::MAX >> 1) + 1).is_none());
        assert!(BitI16::<15>::new((i16::MAX >> 1) + 1).is_none());
        assert!(BitI32::<31>::new((i32::MAX >> 1) + 1).is_none());
        assert!(BitI64::<63>::new((i64::MAX >> 1) + 1).is_none());
        assert!(BitI128::<127>::new((i128::MAX >> 1) + 1).is_none());
    }

    #[test]
    fn get() {
        assert_eq!(BitI8::<7>::MAX.get(), i8::MAX >> 1);
        assert_eq!(BitI16::<15>::MAX.get(), i16::MAX >> 1);
        assert_eq!(BitI32::<31>::MAX.get(), i32::MAX >> 1);
        assert_eq!(BitI64::<63>::MAX.get(), i64::MAX >> 1);
        assert_eq!(BitI128::<127>::MAX.get(), i128::MAX >> 1);
    }

    #[test]
    fn is_positive() {
        assert!(!BitI32::<31>::MIN.is_positive());
        assert!(!BitI32::<31>::default().is_positive());
        assert!(BitI32::<31>::MAX.is_positive());
    }

    #[test]
    fn is_negative() {
        assert!(BitI32::<31>::MIN.is_negative());
        assert!(!BitI32::<31>::default().is_negative());
        assert!(!BitI32::<31>::MAX.is_negative());
    }
}