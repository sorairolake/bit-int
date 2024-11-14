// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(test)]

extern crate test;

use bit_int::{BitI32, BitU32};
use test::Bencher;

#[bench]
fn checked_add_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(42).unwrap();

    b.iter(|| n.checked_add(21));
}

#[bench]
fn checked_add_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(42).unwrap();

    b.iter(|| n.checked_add(21));
}

#[bench]
fn checked_sub_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(-42).unwrap();

    b.iter(|| n.checked_sub(22));
}

#[bench]
fn checked_sub_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(42).unwrap();

    b.iter(|| n.checked_sub(42));
}

#[bench]
fn checked_mul_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(21).unwrap();

    b.iter(|| n.checked_mul(2));
}

#[bench]
fn checked_mul_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(21).unwrap();

    b.iter(|| n.checked_mul(2));
}

#[bench]
fn checked_div_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(42).unwrap();

    b.iter(|| n.checked_div(2));
}

#[bench]
fn checked_div_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(42).unwrap();

    b.iter(|| n.checked_div(2));
}

#[bench]
fn checked_rem_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(5).unwrap();

    b.iter(|| n.checked_rem(2));
}

#[bench]
fn checked_rem_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(5).unwrap();

    b.iter(|| n.checked_rem(2));
}

#[bench]
fn checked_neg_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(5).unwrap();

    b.iter(|| n.checked_neg());
}

#[bench]
fn checked_neg_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::MIN;

    b.iter(|| n.checked_neg());
}

#[bench]
fn checked_abs(b: &mut Bencher) {
    let n = BitI32::<31>::new(-5).unwrap();

    b.iter(|| n.checked_abs());
}

#[bench]
fn checked_pow_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(8).unwrap();

    b.iter(|| n.checked_pow(2));
}

#[bench]
fn checked_pow_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(2).unwrap();

    b.iter(|| n.checked_pow(5));
}
