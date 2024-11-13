// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use bit_int::{BitI32, BitU32};
use test::Bencher;

#[bench]
fn from_bit_int_to_underlying_type(b: &mut Bencher) {
    b.iter(|| i32::from(BitI32::<31>::MAX));
}

#[bench]
fn from_bit_uint_to_underlying_type(b: &mut Bencher) {
    b.iter(|| u32::from(BitU32::<31>::MAX));
}
