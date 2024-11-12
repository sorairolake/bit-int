// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use bit_int::BitU32;
use test::Bencher;

#[bench]
fn default(b: &mut Bencher) {
    b.iter(BitU32::<31>::default);
}

#[bench]
fn new(b: &mut Bencher) {
    b.iter(|| BitU32::<31>::new(u32::MAX >> 1));
}

#[bench]
fn get(b: &mut Bencher) {
    b.iter(|| BitU32::<31>::MAX.get());
}
