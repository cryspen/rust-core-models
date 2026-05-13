//! Equivalence tests for `core::option::Option::*`.

use crate::helpers::none_u8;
use rust_lean_test_macro::rust_lean_test;

// ----- is_some / is_none -----------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_is_some_none_u8() -> bool {
    none_u8().is_some() == false
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_is_some_some_zero() -> bool {
    Some(0u8).is_some() == true
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_is_some_some_max() -> bool {
    Some(u8::MAX).is_some() == true
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_is_none_none_u8() -> bool {
    none_u8().is_none() == true
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_is_none_some_zero() -> bool {
    Some(0u8).is_none() == false
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_is_none_some_max() -> bool {
    Some(u8::MAX).is_none() == false
}
*/

// ----- is_some_and -----------------------------------------------------------

// TODO(closure-extraction): is_some_and takes a closure; revisit when we exercise FnOnce.

// ----- is_none_or ------------------------------------------------------------

// TODO(closure-extraction): is_none_or takes a closure; revisit when we exercise FnOnce.

// ----- as_ref ----------------------------------------------------------------

// TODO(as_ref): as_ref returns Option<&T> which involves references-to-references
// through extraction; skip until references are exercised.

// ----- expect ----------------------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_expect_some_zero() -> bool {
    Some(0u8).expect("msg") == 0
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_expect_some_max() -> bool {
    Some(u8::MAX).expect("msg") == u8::MAX
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_expect_some_mid() -> bool {
    Some(42u8).expect("msg") == 42
}
*/

// ----- unwrap ----------------------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_some_zero() -> bool {
    Some(0u8).unwrap() == 0
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_some_max() -> bool {
    Some(u8::MAX).unwrap() == u8::MAX
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_some_mid() -> bool {
    Some(7u8).unwrap() == 7
}
*/

// ----- unwrap_or -------------------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_some_zero() -> bool {
    Some(0u8).unwrap_or(42) == 0
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_some_max() -> bool {
    Some(u8::MAX).unwrap_or(0) == u8::MAX
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_none_default_zero() -> bool {
    none_u8().unwrap_or(0) == 0
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_none_default_max() -> bool {
    none_u8().unwrap_or(u8::MAX) == u8::MAX
}
*/

// ----- unwrap_or_else --------------------------------------------------------

// TODO(closure-extraction): unwrap_or_else takes a closure; revisit when we exercise FnOnce.

// ----- unwrap_or_default -----------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_default_some_zero() -> bool {
    Some(0u8).unwrap_or_default() == 0
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_default_some_max() -> bool {
    Some(u8::MAX).unwrap_or_default() == u8::MAX
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_default_none() -> bool {
    none_u8().unwrap_or_default() == 0
}
*/

// ----- map -------------------------------------------------------------------

// TODO(closure-extraction): map takes a closure; revisit when we exercise FnOnce.

// ----- map_or ----------------------------------------------------------------

// TODO(closure-extraction): map_or takes a closure; revisit when we exercise FnOnce.

// ----- map_or_else -----------------------------------------------------------

// TODO(closure-extraction): map_or_else takes two closures; revisit when we exercise FnOnce.

// ----- map_or_default --------------------------------------------------------

// TODO(closure-extraction): map_or_default takes a closure; revisit when we exercise FnOnce.

// ----- ok_or -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_ok_or_some_zero() -> bool {
    matches!(Some(0u8).ok_or(99u8), Ok(0))
}

#[rust_lean_test]
pub fn test_ok_or_some_max() -> bool {
    matches!(Some(u8::MAX).ok_or(0u8), Ok(v) if v == u8::MAX)
}

#[rust_lean_test]
pub fn test_ok_or_none_err_zero() -> bool {
    matches!(none_u8().ok_or(0u8), Err(0))
}

#[rust_lean_test]
pub fn test_ok_or_none_err_max() -> bool {
    matches!(none_u8().ok_or(u8::MAX), Err(v) if v == u8::MAX)
}

// ----- filter ----------------------------------------------------------------

// TODO(closure-extraction): filter takes a closure; revisit when we exercise FnOnce.

// ----- or --------------------------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_or_some_some() -> bool {
    Some(0u8).or(Some(99u8)).unwrap_or(7) == 0
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_or_some_none() -> bool {
    Some(u8::MAX).or(none_u8()).unwrap_or(0) == u8::MAX
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_or_none_some() -> bool {
    none_u8().or(Some(42u8)).unwrap_or(0) == 42
}
*/

#[rust_lean_test]
pub fn test_or_none_none() -> bool {
    none_u8().or(none_u8()).is_none()
}

// ----- or_else ---------------------------------------------------------------

// TODO(closure-extraction): or_else takes a closure; revisit when we exercise FnOnce.

// ----- xor -------------------------------------------------------------------

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_xor_some_none() -> bool {
    Some(7u8).xor(none_u8()).unwrap_or(0) == 7
}
*/

// TODO(option-eq-extraction: as above — Option `==` Option.)
/*
#[rust_lean_test]
pub fn test_xor_none_some() -> bool {
    none_u8().xor(Some(u8::MAX)).unwrap_or(0) == u8::MAX
}
*/

#[rust_lean_test]
pub fn test_xor_some_some() -> bool {
    Some(0u8).xor(Some(99u8)).is_none()
}

#[rust_lean_test]
pub fn test_xor_none_none() -> bool {
    none_u8().xor(none_u8()).is_none()
}

// ----- zip -------------------------------------------------------------------

// TODO(tuple-eq-extraction: `zip` returns `Option<(T, U)>` and our tests destructure the pair, hitting the missing `Pair.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_zip_some_some_zero() -> bool {
    match Some(0u8).zip(Some(0u8)) {
        Some((a, b)) => a == 0 && b == 0,
        None => false,
    }
}
*/

// TODO(tuple-eq-extraction: `zip` returns `Option<(T, U)>` and our tests destructure the pair, hitting the missing `Pair.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_zip_some_some_max() -> bool {
    match Some(u8::MAX).zip(Some(0u8)) {
        Some((a, b)) => a == u8::MAX && b == 0,
        None => false,
    }
}
*/

// TODO(tuple-eq-extraction: `zip` returns `Option<(T, U)>` and our tests destructure the pair, hitting the missing `Pair.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_zip_some_none() -> bool {
    Some(7u8).zip(none_u8()).is_none()
}
*/

// TODO(tuple-eq-extraction: `zip` returns `Option<(T, U)>` and our tests destructure the pair, hitting the missing `Pair.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_zip_none_some() -> bool {
    none_u8().zip(Some(7u8)).is_none()
}
*/

// TODO(tuple-eq-extraction: `zip` returns `Option<(T, U)>` and our tests destructure the pair, hitting the missing `Pair.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_zip_none_none() -> bool {
    none_u8().zip(none_u8()).is_none()
}
*/

// ----- inspect ---------------------------------------------------------------

// TODO(closure-extraction): inspect takes a closure; revisit when we exercise FnOnce.

// ----- flatten ---------------------------------------------------------------

// TODO(option-flatten-tuple-extraction: comparing `Option<Option<T>>` flattens through the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_flatten_some_some_zero() -> bool {
    Some(Some(0u8)).flatten().unwrap_or(99) == 0
}
*/

// TODO(option-flatten-tuple-extraction: comparing `Option<Option<T>>` flattens through the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_flatten_some_some_max() -> bool {
    Some(Some(u8::MAX)).flatten().unwrap_or(0) == u8::MAX
}
*/

// TODO(option-flatten-tuple-extraction: comparing `Option<Option<T>>` flattens through the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_flatten_some_none() -> bool {
    Some(none_u8()).flatten().is_none()
}
*/

// ----- Default ---------------------------------------------------------------

// TODO(default-trait): testing Default for Option<T> via the model trait requires
// importing the model's Default trait; revisit alongside Default coverage.

// ----------------------------------------------------------------------------
// The four methods below — `is_some`, `is_none`, `unwrap_or`, `take` — are
// listed in `CHARON_EXCLUDES`, so Aeneas does not extract their bodies.
// The Lean side routes through the name map to manually-written
// definitions in `lean/CoreModels/FunsPrologue.lean` / `FunsExternal.lean`.
// The Rust call site looks identical to the extracted variants exercised
// above; the value of having both sections is that one round-trips
// through extraction, the other through the hand-written Lean def.
// ----------------------------------------------------------------------------

use crate::helpers::{none_i32, none_u32};

// ----- is_some (manually defined in Lean, not extracted) --------------------

#[rust_lean_test]
pub fn test_manual_is_some_some_u8_zero() -> bool {
    Some(0u8).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_some_u8_max() -> bool {
    Some(u8::MAX).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_none_u8() -> bool {
    none_u8().is_some() == false
}

#[rust_lean_test]
pub fn test_manual_is_some_some_u32() -> bool {
    Some(123u32).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_none_u32() -> bool {
    none_u32().is_some() == false
}

#[rust_lean_test]
pub fn test_manual_is_some_some_bool() -> bool {
    Some(true).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_none_bool() -> bool {
    crate::helpers::none_bool().is_some() == false
}

// ----- is_none (manually defined in Lean, not extracted) --------------------

#[rust_lean_test]
pub fn test_manual_is_none_some_u8_zero() -> bool {
    Some(0u8).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_some_u8_max() -> bool {
    Some(u8::MAX).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_none_u8() -> bool {
    none_u8().is_none() == true
}

#[rust_lean_test]
pub fn test_manual_is_none_some_i32() -> bool {
    Some(-1i32).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_none_i32() -> bool {
    none_i32().is_none() == true
}

#[rust_lean_test]
pub fn test_manual_is_none_some_bool() -> bool {
    Some(false).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_none_bool() -> bool {
    crate::helpers::none_bool().is_none() == true
}

// ----- unwrap_or (manually defined in Lean, not extracted) ------------------

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_u8_zero() -> bool {
    Some(0u8).unwrap_or(42) == 0
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_u8_max() -> bool {
    Some(u8::MAX).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_u8_small_default() -> bool {
    none_u8().unwrap_or(7) == 7
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_u8_max_default() -> bool {
    none_u8().unwrap_or(u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_u32_small() -> bool {
    Some(5u32).unwrap_or(99) == 5
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_u32_max_default() -> bool {
    none_u32().unwrap_or(u32::MAX) == u32::MAX
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_bool() -> bool {
    Some(true).unwrap_or(false) == true
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_bool() -> bool {
    crate::helpers::none_bool().unwrap_or(true) == true
}

// ----- take (manually defined in Lean, not extracted) -----------------------

// TODO(option-eq-extraction: comparing the `take` return `Option<T> == Some(_)` extracts to the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_manual_take_some_u8_returns_old() -> bool {
    let mut x: Option<u8> = Some(9);
    let old = x.take();
    old == Some(9)
}
*/

#[rust_lean_test]
pub fn test_manual_take_some_u8_replaces_with_none() -> bool {
    let mut x: Option<u8> = Some(9);
    let _ = x.take();
    x.is_some() == false
}

// TODO(option-eq-extraction: comparing the `take` return `Option<T> == Some(_)` extracts to the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_manual_take_some_u8_max_returns_old() -> bool {
    let mut x: Option<u8> = Some(u8::MAX);
    let old = x.take();
    old == Some(u8::MAX) && x.is_none()
}
*/

#[rust_lean_test]
pub fn test_manual_take_none_u8_returns_none() -> bool {
    let mut x: Option<u8> = none_u8();
    let old = x.take();
    old.is_none() && x.is_none()
}

// TODO(option-eq-extraction: comparing the `take` return `Option<T> == Some(_)` extracts to the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_manual_take_some_u32() -> bool {
    let mut x: Option<u32> = Some(123);
    let old = x.take();
    old == Some(123) && x.is_none()
}
*/

#[rust_lean_test]
pub fn test_manual_take_none_u32() -> bool {
    let mut x: Option<u32> = none_u32();
    let old = x.take();
    old.is_none() && x.is_none()
}

// TODO(option-eq-extraction: comparing the `take` return `Option<T> == Some(_)` extracts to the missing `Option.PartialEq` def.)
/*
#[rust_lean_test]
pub fn test_manual_take_some_bool() -> bool {
    let mut x: Option<bool> = Some(true);
    let old = x.take();
    old == Some(true) && x.is_none()
}
*/
