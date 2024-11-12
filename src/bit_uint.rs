// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! An arbitrary fixed bit-width unsigned integer.

mod cmp;
mod consts;
mod fmt;
mod ops;

use num_traits::{PrimInt, Unsigned};

/// `BitUint` is a type that represents a `N`-bit unsigned integer.
///
/// The largest size of `N` is equal to the size of the underlying type in bits.
///
/// # Examples
///
/// ```compile_fail
/// use bit_int::BitUint;
///
/// let n = BitUint::<u32, 33>::new(42);
/// assert_eq!(n.map(BitUint::get), Some(42));
/// ```
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BitUint<T: Unsigned + PrimInt, const N: u32>(T);

macro_rules! impl_bit_uint {
    ($T:ty, $alias:ident) => {
        impl<const N: u32> BitUint<$T, N> {
            /// Creates a new `BitUint` with the given unsigned integer value.
            ///
            /// Returns [`None`] if the value is not a valid `N`-bit unsigned integer.
            ///
            /// # Examples
            ///
            /// ```
            /// # use bit_int::BitUint;
            /// #
            #[doc = concat!("let n = BitUint::<", stringify!($T), ", 6>::new(42);")]
            /// assert_eq!(n.map(BitUint::get), Some(42));
            #[doc = ""]
            #[doc = concat!("let m = BitUint::<", stringify!($T), ", 5>::new(42);")]
            /// assert!(m.is_none());
            /// ```
            #[must_use]
            #[inline]
            pub const fn new(n: $T) -> Option<Self> {
                // `n` must be greater than or equal to 0.
                debug_assert!(n >= Self::MIN.get());

                if n <= Self::MAX.get() {
                    // SAFETY: `n` is checked to be a valid `N`-bit unsigned integer.
                    let n = unsafe { Self::new_unchecked(n) };
                    Some(n)
                } else {
                    None
                }
            }
        }

        /// A specialized [`BitUint`] type whose the underlying type is restricted to
        #[doc = concat!("[`", stringify!($T), "`].")]
        ///
        #[doc = concat!("The largest size of `N` is equal to [`", stringify!($T), "::BITS`].")]
        pub type $alias<const N: u32> = BitUint<$T, N>;
    };
}
impl_bit_uint!(u8, BitU8);
impl_bit_uint!(u16, BitU16);
impl_bit_uint!(u32, BitU32);
impl_bit_uint!(u64, BitU64);
impl_bit_uint!(u128, BitU128);
impl_bit_uint!(usize, BitUsize);

impl<T: Unsigned + PrimInt, const N: u32> BitUint<T, N> {
    /// Creates a new `BitUint` with the given unsigned integer value.
    ///
    /// This method does not check whether the value is a valid `N`-bit unsigned
    /// integer. This results in undefined behaviour if the value is not a valid
    /// `N`-bit unsigned integer.
    ///
    /// # Safety
    ///
    /// The value must be a valid `N`-bit unsigned integer.
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
            any::type_name::<BitU8::<7>>(),
            any::type_name::<BitUint::<u8, 7>>()
        );
        assert_eq!(
            any::type_name::<BitU16::<15>>(),
            any::type_name::<BitUint::<u16, 15>>()
        );
        assert_eq!(
            any::type_name::<BitU32::<31>>(),
            any::type_name::<BitUint::<u32, 31>>()
        );
        assert_eq!(
            any::type_name::<BitU64::<63>>(),
            any::type_name::<BitUint::<u64, 63>>()
        );
        assert_eq!(
            any::type_name::<BitU128::<127>>(),
            any::type_name::<BitUint::<u128, 127>>()
        );
        assert_eq!(
            any::type_name::<BitUsize::<31>>(),
            any::type_name::<BitUint::<usize, 31>>()
        );
    }

    #[test]
    fn layout() {
        assert_eq!(mem::size_of::<BitU32::<31>>(), mem::size_of::<u32>());
        assert_eq!(mem::align_of::<BitU32::<31>>(), mem::align_of::<u32>());
    }

    #[test]
    fn clone() {
        assert_eq!(BitU32::<31>::MIN.clone(), BitU32::<31>::MIN);
    }

    #[test]
    fn copy() {
        let a = BitU32::<31>::MIN;
        let b = a;
        assert_eq!(a, b);
    }

    #[test]
    fn default() {
        assert_eq!(
            BitU32::<31>::default(),
            BitU32::<31>::new(u32::default()).unwrap()
        );
    }

    #[test]
    fn new() {
        assert_eq!(
            BitU8::<7>::new(u8::MAX >> 1).map(BitU8::get),
            Some(u8::MAX >> 1)
        );
        assert_eq!(
            BitU16::<15>::new(u16::MAX >> 1).map(BitU16::get),
            Some(u16::MAX >> 1)
        );
        assert_eq!(
            BitU32::<31>::new(u32::MAX >> 1).map(BitU32::get),
            Some(u32::MAX >> 1)
        );
        assert_eq!(
            BitU64::<63>::new(u64::MAX >> 1).map(BitU64::get),
            Some(u64::MAX >> 1)
        );
        assert_eq!(
            BitU128::<127>::new(u128::MAX >> 1).map(BitU128::get),
            Some(u128::MAX >> 1)
        );
    }

    #[test]
    fn new_with_invalid_value() {
        assert!(BitU8::<7>::new((u8::MAX >> 1) + 1).is_none());
        assert!(BitU16::<15>::new((u16::MAX >> 1) + 1).is_none());
        assert!(BitU32::<31>::new((u32::MAX >> 1) + 1).is_none());
        assert!(BitU64::<63>::new((u64::MAX >> 1) + 1).is_none());
        assert!(BitU128::<127>::new((u128::MAX >> 1) + 1).is_none());
    }

    #[test]
    const fn new_is_const_fn() {
        const _: Option<BitU32<31>> = BitU32::<31>::new(u32::MAX >> 1);
    }

    #[test]
    fn new_unchecked() {
        assert_eq!(
            unsafe { BitU8::<7>::new_unchecked(u8::MAX >> 1) }.get(),
            u8::MAX >> 1
        );
        assert_eq!(
            unsafe { BitU16::<15>::new_unchecked(u16::MAX >> 1) }.get(),
            u16::MAX >> 1
        );
        assert_eq!(
            unsafe { BitU32::<31>::new_unchecked(u32::MAX >> 1) }.get(),
            u32::MAX >> 1
        );
        assert_eq!(
            unsafe { BitU64::<63>::new_unchecked(u64::MAX >> 1) }.get(),
            u64::MAX >> 1
        );
        assert_eq!(
            unsafe { BitU128::<127>::new_unchecked(u128::MAX >> 1) }.get(),
            u128::MAX >> 1
        );
    }

    #[test]
    const fn new_unchecked_is_const_fn() {
        const _: BitU32<31> = unsafe { BitU32::<31>::new_unchecked(u32::MAX >> 1) };
    }

    #[test]
    fn get() {
        assert_eq!(BitU8::<7>::MAX.get(), u8::MAX >> 1);
        assert_eq!(BitU16::<15>::MAX.get(), u16::MAX >> 1);
        assert_eq!(BitU32::<31>::MAX.get(), u32::MAX >> 1);
        assert_eq!(BitU64::<63>::MAX.get(), u64::MAX >> 1);
        assert_eq!(BitU128::<127>::MAX.get(), u128::MAX >> 1);
    }

    #[test]
    const fn get_is_const_fn() {
        const _: u32 = BitU32::<31>::MIN.get();
    }
}
