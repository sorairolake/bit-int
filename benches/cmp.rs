// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use bit_int::{BitI32, BitU32};
use test::Bencher;

#[bench]
fn equality_bit_int(b: &mut Bencher) {
    b.iter(|| BitI32::<31>::MIN == BitI32::<31>::MIN);
}

#[bench]
fn equality_bit_uint(b: &mut Bencher) {
    b.iter(|| BitU32::<31>::MIN == BitU32::<31>::MIN);
}

#[bench]
fn order_bit_int(b: &mut Bencher) {
    b.iter(|| BitI32::<31>::MIN < BitI32::<31>::MAX);
}

#[bench]
fn order_bit_uint(b: &mut Bencher) {
    b.iter(|| BitU32::<31>::MIN < BitU32::<31>::MAX);
}
