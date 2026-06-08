/// See [`core::intrinsics::unreachable`]. Reaching this is undefined behaviour
/// in Rust; in the model we treat it as an (unreachable) panic, with a
/// `requires(false)` precondition so callers must prove it is never hit.
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn unreachable() -> ! {
    panic!()
}
