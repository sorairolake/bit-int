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
fn checked_div_euclid_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(42).unwrap();

    b.iter(|| n.checked_div_euclid(2));
}

#[bench]
fn checked_div_euclid_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(42).unwrap();

    b.iter(|| n.checked_div_euclid(2));
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
fn checked_rem_euclid_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(5).unwrap();

    b.iter(|| n.checked_rem_euclid(2));
}

#[bench]
fn checked_rem_euclid_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(5).unwrap();

    b.iter(|| n.checked_rem_euclid(2));
}

#[bench]
fn checked_ilog_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(5).unwrap();

    b.iter(|| n.checked_ilog(5));
}

#[bench]
fn checked_ilog_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(5).unwrap();

    b.iter(|| n.checked_ilog(5));
}

#[bench]
fn checked_ilog2_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(2).unwrap();

    b.iter(|| n.checked_ilog2());
}

#[bench]
fn checked_ilog2_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(2).unwrap();

    b.iter(|| n.checked_ilog2());
}

#[bench]
fn checked_ilog10_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(10).unwrap();

    b.iter(|| n.checked_ilog10());
}

#[bench]
fn checked_ilog10_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(10).unwrap();

    b.iter(|| n.checked_ilog10());
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
fn checked_shl_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(0x01).unwrap();

    b.iter(|| n.checked_shl(4));
}

#[bench]
fn checked_shl_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(0x01).unwrap();

    b.iter(|| n.checked_shl(4));
}

#[bench]
fn checked_shr_bit_int(b: &mut Bencher) {
    let n = BitI32::<31>::new(0x10).unwrap();

    b.iter(|| n.checked_shr(4));
}

#[bench]
fn checked_shr_bit_uint(b: &mut Bencher) {
    let n = BitU32::<31>::new(0x10).unwrap();

    b.iter(|| n.checked_shr(4));
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
