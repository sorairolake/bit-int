// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `bit-int` crate is a library for providing arbitrary fixed bit-width
//! integers.

#![doc(html_root_url = "https://docs.rs/bit-int/0.1.0/")]
#![no_std]
// Lint levels of rustc.
#![deny(missing_docs)]

#[allow(missing_docs)]
#[must_use]
pub const fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
