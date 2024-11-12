// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use bit_int::BitI32;
use test::Bencher;

#[bench]
fn default(b: &mut Bencher) {
    b.iter(BitI32::<31>::default);
}

#[bench]
fn new(b: &mut Bencher) {
    b.iter(|| BitI32::<31>::new(i32::MAX >> 1));
}

#[bench]
fn get(b: &mut Bencher) {
    b.iter(|| BitI32::<31>::MAX.get());
}

#[bench]
fn is_positive(b: &mut Bencher) {
    b.iter(|| BitI32::<31>::MIN.is_positive());
}

#[bench]
fn is_negative(b: &mut Bencher) {
    b.iter(|| BitI32::<31>::MIN.is_negative());
}
