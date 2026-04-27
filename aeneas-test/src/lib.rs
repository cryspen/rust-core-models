//! Regression-testing crate for the `core-models` Lean library.
//!
//! Each function exercises a `std`-side type or method that downstream
//! users will write naturally. Aeneas extracts this crate and resolves
//! every reference through its **builtin name map** (i.e. the `std::*`
//! → `core.*` / `alloc.*` mappings), then we compile the extracted
//! Lean against our hand-written `Aeneas` library. If something is
//! missing in our shims, it shows up here as a Lean elaboration error.
//!
//! The companion `test-suite/` crate exercises items from the local
//! `core_models` source — i.e. the *extraction* side. This crate
//! exercises the *consumption* side. Both are needed: a name map can
//! point to a Lean symbol that exists for `core_models::*` extraction
//! but not for downstream `std::*` use, and vice versa.

#![allow(dead_code)]

// ----- Arrays ---------------------------------------------------------------

/// Direct usage of `std::array::from_fn` — exercises the `Fn`/`FnMut`
/// trait dispatch. The std signature is `F: FnMut`; Aeneas's name map
/// reaches into the `Fn` instance via its `.FnMutInst` super-trait
/// projection, so our `core.ops.function.Fn` structure must expose
/// that field.
pub fn array_from_fn<T, F: Fn(usize) -> T>(f: F) -> [T; 10] {
    std::array::from_fn(f)
}

/// Closure as `Fn` — `f0` defines a closure inline and feeds it to
/// `array_from_fn`. Hits the auto-derived `core.ops.function.Fn` impl
/// for closures.
pub fn array_from_fn_closure() -> [usize; 10] {
    std::array::from_fn(|x: usize| x)
}

/// Array indexing **returning a reference** — covers
/// `<[T; N] as Index<usize>>::index` (extracts to `core.array.Array.index`
/// or similar via Aeneas's name map).
pub fn array_index_ref(a: &[u8; 10], i: usize) -> &u8 {
    &a[i]
}

/// Array indexing returning by value (Copy types).
pub fn array_index_val(a: [u32; 4], i: usize) -> u32 {
    a[i]
}

// ----- Result ---------------------------------------------------------------

/// `Result::ok` — converts `Result<T,E>` to `Option<T>`. Hits our
/// `core.result.Result.ok` shim in `Primitives.lean`.
pub fn result_ok(x: Result<u8, u8>) -> Option<u8> {
    x.ok()
}

/// `Result::err` — symmetric to `ok`.
pub fn result_err(x: Result<u8, u32>) -> Option<u32> {
    x.err()
}

/// `Result::unwrap` / `is_ok` / `is_err` (only the side we model
/// explicitly).
pub fn result_is_ok(x: Result<u8, u8>) -> bool {
    x.is_ok()
}

pub fn result_is_err(x: Result<u8, u8>) -> bool {
    x.is_err()
}

/// Pattern matching on `Result` — exercises the `Ok`/`Err` constructor
/// abbrevs in our guard namespace.
pub fn result_pattern(x: Result<u8, u8>) -> u8 {
    match x {
        Ok(v) => v,
        Err(_) => 0,
    }
}

// ----- Option ---------------------------------------------------------------

pub fn option_unwrap(x: Option<u8>) -> u8 {
    x.unwrap()
}

pub fn option_unwrap_or(x: Option<u8>, default: u8) -> u8 {
    x.unwrap_or(default)
}

pub fn option_is_some(x: Option<u32>) -> bool {
    x.is_some()
}

pub fn option_is_none(x: Option<u32>) -> bool {
    x.is_none()
}

pub fn option_take(x: &mut Option<u16>) -> Option<u16> {
    x.take()
}

pub fn option_pattern(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

// ----- Slices ---------------------------------------------------------------

pub fn slice_len(x: &[u8]) -> usize {
    x.len()
}

// NOTE: slice indexing through `SliceIndex` is currently excluded from
// our extraction (see `CHARON_EXCLUDES` in the parent Makefile).
// Re-enable the tests below once solution 1 (full SliceIndex modeling
// — `Sealed` super-trait, `get_mut`/`index_mut` back-edges, raw-pointer
// `get_unchecked*`) lands. Each function corresponds to one of the
// `core.slice.index.SliceIndex<X>Slice` aliases that StdAliases.lean
// keeps as a commented-out TODO.
//
//   pub fn slice_index_usize(x: &[u8]) -> u8         { x[0] }
//   pub fn slice_index_range(x: &[u8]) -> &[u8]      { &x[1..3] }
//   pub fn slice_index_range_from(x: &[u8]) -> &[u8] { &x[2..] }
//   pub fn slice_index_range_to(x: &[u8]) -> &[u8]   { &x[..3] }
//   pub fn slice_index_range_full(x: &[u8]) -> &[u8] { &x[..] }

// ----- Vec ------------------------------------------------------------------

// Same gating: `Vec::index` is excluded via ALLOC_CHARON_EXCLUDES.
//
//   pub fn vec_index_usize(x: &Vec<usize>) -> usize { x[0] }
//   pub fn vec_index_and_len(x: Vec<usize>) -> usize { x[0] + x.len() }
//   pub fn vec_index_range(x: &Vec<u8>) -> &[u8] { &x[1..3] }

pub fn vec_new() -> Vec<u32> {
    Vec::new()
}

pub fn vec_with_capacity(c: usize) -> Vec<u8> {
    Vec::with_capacity(c)
}

pub fn vec_push(mut v: Vec<u32>, x: u32) -> Vec<u32> {
    v.push(x);
    v
}

pub fn vec_len(v: &Vec<u32>) -> usize {
    v.len()
}

pub fn vec_from_elem(x: u32, n: usize) -> Vec<u32> {
    vec![x; n]
}

// ----- Closures and higher-order -------------------------------------------

/// `FnMut` as an argument — Aeneas reaches super-trait `FnMut` via
/// `Fn::FnMutInst` when calling `array::from_fn`.
pub fn call_fn<F: Fn(u8) -> u8>(f: F, x: u8) -> u8 {
    f(x)
}

pub fn call_fn_mut<F: FnMut(u8) -> u8>(mut f: F, x: u8) -> u8 {
    f(x)
}

// ----- Ranges --------------------------------------------------------------

pub fn range_sum(n: usize) -> usize {
    let mut acc: usize = 0;
    for i in 0..n {
        acc = acc.wrapping_add(i);
    }
    acc
}

// ----- Scalar arithmetic ---------------------------------------------------

pub fn add_u8(x: u8, y: u8) -> u8 {
    x + y
}

pub fn sub_u32(x: u32, y: u32) -> u32 {
    x - y
}

pub fn lt_u8(x: u8, y: u8) -> bool {
    x < y
}

pub fn ge_usize(x: usize, y: usize) -> bool {
    x >= y
}

pub fn xor_u64(x: u64, y: u64) -> u64 {
    x ^ y
}

// ----- Mem -----------------------------------------------------------------

pub fn mem_swap_u32(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b);
}

pub fn mem_replace_u8(dst: &mut u8, src: u8) -> u8 {
    core::mem::replace(dst, src)
}

// ----- Clone / Copy --------------------------------------------------------

pub fn clone_u64(x: u64) -> u64 {
    x.clone()
}

pub fn copy_u8(x: u8) -> (u8, u8) {
    (x, x)
}

// ----- Box -----------------------------------------------------------------

pub fn box_new(x: u32) -> Box<u32> {
    Box::new(x)
}

pub fn box_deref(b: &Box<u8>) -> u8 {
    **b
}
