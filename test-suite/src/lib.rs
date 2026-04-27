//! Test suite for the `core-models` Lean library.
//!
//! Each function below exercises one or more items from `core` that are
//! modeled in `core-models` and provided as Lean definitions in the
//! sibling `Aeneas` library. Aeneas extracts this crate to Lean; we then
//! verify that the extracted code compiles against our hand-written
//! `Aeneas` package.

#![allow(dead_code)]

// ----- Option ---------------------------------------------------------------

pub fn opt_unwrap_or(x: Option<u8>, default: u8) -> u8 {
    x.unwrap_or(default)
}

pub fn opt_is_some(x: Option<u32>) -> bool {
    x.is_some()
}

pub fn opt_is_none(x: Option<u32>) -> bool {
    x.is_none()
}

pub fn opt_take(x: &mut Option<u16>) -> Option<u16> {
    x.take()
}

// ----- mem ------------------------------------------------------------------

pub fn mem_swap_u32(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b);
}

pub fn mem_replace_u8(dst: &mut u8, src: u8) -> u8 {
    core::mem::replace(dst, src)
}

// ----- Scalar arithmetic ----------------------------------------------------

pub fn add_u8(x: u8, y: u8) -> u8 {
    x + y
}

pub fn sub_u32(x: u32, y: u32) -> u32 {
    x - y
}

pub fn mul_u16(x: u16, y: u16) -> u16 {
    x * y
}

// ----- Comparisons ----------------------------------------------------------

pub fn lt_u8(x: u8, y: u8) -> bool {
    x < y
}

pub fn ge_usize(x: usize, y: usize) -> bool {
    x >= y
}

// ----- Pattern matching on Option -------------------------------------------

pub fn opt_double(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v.wrapping_add(v),
        None => 0,
    }
}

// ----- Bitwise (XOR / OR / AND on scalars) ----------------------------------

pub fn xor_u64(x: u64, y: u64) -> u64 {
    x ^ y
}

pub fn or_u32(x: u32, y: u32) -> u32 {
    x | y
}

pub fn and_u8(x: u8, y: u8) -> u8 {
    x & y
}

// ----- Clone / Copy on scalars ----------------------------------------------

pub fn clone_u64(x: u64) -> u64 {
    x.clone()
}

pub fn copy_u8(x: u8) -> (u8, u8) {
    (x, x)
}

// ----- Arrays ---------------------------------------------------------------

pub fn arr_index(a: [u32; 4], i: usize) -> u32 {
    a[i]
}

pub fn arr_set(mut a: [u32; 4], i: usize, x: u32) -> [u32; 4] {
    a[i] = x;
    a
}

pub fn arr_repeat() -> [u8; 16] {
    [0u8; 16]
}

// ----- Range iteration -----------------------------------------------------

/// Exercises `core::iter::range::IteratorRange::next` (the iterator that
/// drives `for i in 0..n` loops over `Range<usize>`).
pub fn range_sum(n: usize) -> usize {
    let mut acc: usize = 0;
    for i in 0..n {
        acc = acc.wrapping_add(i);
    }
    acc
}

/// Triggers `Array.make` with a 24-element initializer (regression test for
/// the default proof tactic — `by rfl` cannot reduce `(Usize.ofNat 24).val`
/// to `24`, only `by simp` with the right lemmas can).
pub const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

pub fn arr_to_slice(a: &[u32; 4]) -> &[u32] {
    a
}

// ----- alloc::vec::Vec ------------------------------------------------------
//
// Uses the standard `Vec` (re-exported from `alloc` via `std`). Charon emits
// these as references to `alloc::vec::Vec::*`, which Aeneas resolves against
// its builtin name map. The methods below cover everything our extracted
// `Aeneas/Alloc/Funs.lean` provides.

// --- pure shape (Aeneas marks `~can_fail:false ~lift:false`) ---

pub fn vec_new_u32() -> Vec<u32> {
    Vec::new()
}

pub fn vec_with_capacity_u8(c: usize) -> Vec<u8> {
    Vec::with_capacity(c)
}

pub fn vec_len_u32(v: &Vec<u32>) -> usize {
    v.len()
}

// --- monadic shape (push/insert/resize/extend_from_slice) ---

pub fn vec_push_one(mut v: Vec<u32>, x: u32) -> Vec<u32> {
    v.push(x);
    v
}

pub fn vec_push_two(mut v: Vec<u8>, x: u8, y: u8) -> Vec<u8> {
    v.push(x);
    v.push(y);
    v
}

pub fn vec_insert_u8(mut v: Vec<u8>, i: usize, x: u8) -> Vec<u8> {
    v.insert(i, x);
    v
}

pub fn vec_extend_from_slice_u8(mut v: Vec<u8>, s: &[u8]) -> Vec<u8> {
    v.extend_from_slice(s);
    v
}

// --- vec::from_elem ---
//
// `vec![x; n]` lowers to a call to `alloc::vec::from_elem`.

pub fn vec_from_elem_u32(x: u32, n: usize) -> Vec<u32> {
    vec![x; n]
}

// --- alloc::slice methods ---
//
// `[T]::to_vec` and `[T]::into_vec` are in Aeneas's builtin map.

pub fn slice_to_vec_u8(s: &[u8]) -> Vec<u8> {
    s.to_vec()
}

// --- alloc::boxed::Box ---
//
// Hax/Aeneas erase `Box<T>` to `T`, but we still want to make sure the
// surface compiles end-to-end.

pub fn box_new_u32(x: u32) -> Box<u32> {
    Box::new(x)
}

pub fn box_deref_u8(b: &Box<u8>) -> u8 {
    **b
}
