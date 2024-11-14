// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `bit-int` crate is a library for providing arbitrary fixed bit-width
//! integers.
//!
//! The value is represented by either of the following types:
//!
//! - The [`BitInt`] type represents a `N`-bit signed integer. This type is
//!   similar to `signed _BitInt(n)` in [C23], or arbitrary fixed bit-width
//!   signed integer types (e.g., `i7`) in [Zig].
//! - The [`BitUint`] type represents a `N`-bit unsigned integer. This type is
//!   similar to `unsigned _BitInt(n)` in C23, or arbitrary fixed bit-width
//!   unsigned integer types (e.g., `u7`) in Zig.
//!
//! The largest size of `N` depends on the size of the underlying type in bits.
//! Therefore, when the underlying type of [`BitInt`] is [`i32`], the largest
//! size of `N` is [`i32::BITS`], and when the underlying type of [`BitUint`] is
//! [`u64`], the largest size of `N` is [`u64::BITS`].
//!
//! # Examples
//!
//! ## Signed integer type
//!
//! ```
//! use bit_int::BitInt;
//!
//! type Int = BitInt<i8, 7>;
//!
//! let n = Int::MIN;
//! assert_eq!(format!("{n}"), "-64");
//!
//! let n = n.checked_add(106).unwrap();
//! // Gets the contained value as the underlying type.
//! assert_eq!(n.get(), 42);
//!
//! let n = n.checked_add(21).unwrap();
//! assert_eq!(n.get(), 63);
//! assert_eq!(n, Int::MAX);
//!
//! assert!(n.checked_add(22).is_none());
//! ```
//!
//! ## Unsigned integer type
//!
//! ```
//! use bit_int::BitUint;
//!
//! type Uint = BitUint<u8, 7>;
//!
//! let n = Uint::MIN;
//! assert_eq!(format!("{n}"), "0");
//!
//! let n = n.checked_add(42).unwrap();
//! // Gets the contained value as the underlying type.
//! assert_eq!(n.get(), 42);
//!
//! let n = n.checked_add(85).unwrap();
//! assert_eq!(n.get(), 127);
//! assert_eq!(n, Uint::MAX);
//!
//! assert!(n.checked_add(86).is_none());
//! ```
//!
//! [C23]: https://en.cppreference.com/w/c/23
//! [Zig]: https://ziglang.org/

#![doc(html_root_url = "https://docs.rs/bit-int/0.1.1/")]
#![no_std]
// Lint levels of rustc.
#![deny(missing_docs)]

#[cfg(test)]
#[macro_use]
extern crate alloc;

mod bit_int;
mod bit_uint;

pub use crate::{
    bit_int::{BitI128, BitI16, BitI32, BitI64, BitI8, BitInt, BitIsize},
    bit_uint::{BitU128, BitU16, BitU32, BitU64, BitU8, BitUint, BitUsize},
};
