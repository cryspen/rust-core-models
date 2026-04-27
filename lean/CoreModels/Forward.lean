/-
Forward declarations for items in the `core.*` namespace that Aeneas does
not already ship in its standard library.

Audit summary (compared against `Aeneas/Std/Core/*` in the upstream repo):

  ALREADY PROVIDED BY AENEAS — do NOT redeclare:
    • core.clone.Clone, core.clone.Clone{Bool,U8,U16,U32,U64,U128,Usize,
        I8,I16,I32,I64,I128,Isize}
    • core.marker.Copy, core.marker.CopyBool
    • core.option.Option (via attribute → Lean's `Option`),
        Option.{is_some,is_none,unwrap,unwrap_or,take,expect}
    • core.ops.function.{Fn, FnMut, FnOnce}
    • core.cmp.PartialEq, core.cmp.impls.PartialEq{Unit,Bool}
    • core.num.<X>.{MIN,MAX} for every scalar type
    • Aeneas.Std.{U8,U16,U32,U64,U128,Usize,I8,...,Isize}, the bound types,
      Result/ok/fail/div/Bind/Monad, Slice, Array, Error, ControlFlow.loop
    • The `rust_type` / `rust_fun` / `rust_trait` / `rust_trait_impl` /
      `rust_const` attributes (Aeneas.Tactic.RustAttributes)

  STILL NEEDED (not in Aeneas):
    • core.Phantom (non-reducible structure for the alloc Vec rewrite)
    • core.Dyn (trait-object wrapper)
    • core.{Mut,Const}RawPtr (we keep them as 1-arg aliases over T;
      Aeneas's Aeneas.Std.{Mut,Const}RawPtr live at a different path)
    • core.cmp.impls.PartialEq{U8,U16,U32,U64,U128,Usize,I8,I16,I32,I64,
      I128,Isize} (Aeneas only ships Unit/Bool variants)
    • core.marker.Copy{U8,...,Isize} (same gap as PartialEq)
    • The `discriminant` attribute (verify this is missing upstream)

Anything else generated extraction needs is either modeled by your local
`core_models` Rust crate (so it falls out of extraction) or by Aeneas
directly (so `import Aeneas` puts it in scope).
-/

import Aeneas

open Aeneas Aeneas.Std

namespace core

/-! ## Phantom marker

A non-reducible structure with a phantom type parameter. The
non-reducibility is load-bearing: a `def` would let Lean unfold the alias
and lose `A` during unification, breaking the `{A : Type}` implicit at
call sites like `alloc.vec.Vec.clear v`.
-/

structure Phantom (A : Type) where mk ::

/-! ## `dyn Trait` trait objects

Pairs an underlying type with a value of that type and the corresponding
trait instance, erasing it behind an existential wrapper. Aeneas extracts
Rust's `dyn Trait` types as `Dyn (fun _dyn => Trait _dyn)`.
-/

structure Dyn (F : Type → Type) where
  Self : Type
  value : Self
  inst : F Self

/-! ## Raw pointers

Opaque 1-arg aliases over the pointee type. Aeneas's own `Aeneas.Std.MutRawPtr`
lives at a different path (`Aeneas.Std.RawPtr T .Mut`) and isn't reachable as
`core.MutRawPtr`, so we expose our own short alias here.
-/

def ConstRawPtr (T : Type) : Type := T
def MutRawPtr   (T : Type) : Type := T

end core

/-! ## Scalar `Copy` instances

Aeneas ships only `core.marker.CopyBool`. Our extracted code references
`core.marker.Copy{U8,...,Isize}` everywhere; build them on top of the
`Clone` instances Aeneas already provides.
-/

namespace core.marker

def CopyU8    : core.marker.Copy U8    := { cloneInst := core.clone.CloneU8 }
def CopyU16   : core.marker.Copy U16   := { cloneInst := core.clone.CloneU16 }
def CopyU32   : core.marker.Copy U32   := { cloneInst := core.clone.CloneU32 }
def CopyU64   : core.marker.Copy U64   := { cloneInst := core.clone.CloneU64 }
def CopyU128  : core.marker.Copy U128  := { cloneInst := core.clone.CloneU128 }
def CopyUsize : core.marker.Copy Usize := { cloneInst := core.clone.CloneUsize }
def CopyI8    : core.marker.Copy I8    := { cloneInst := core.clone.CloneI8 }
def CopyI16   : core.marker.Copy I16   := { cloneInst := core.clone.CloneI16 }
def CopyI32   : core.marker.Copy I32   := { cloneInst := core.clone.CloneI32 }
def CopyI64   : core.marker.Copy I64   := { cloneInst := core.clone.CloneI64 }
def CopyI128  : core.marker.Copy I128  := { cloneInst := core.clone.CloneI128 }
def CopyIsize : core.marker.Copy Isize := { cloneInst := core.clone.CloneIsize }

end core.marker

/-! ## Scalar `PartialEq` impls

Aeneas ships only `core.cmp.impls.PartialEq{Unit,Bool}`. Generated code
emitted by our `core_models` cmp extraction refers to scalar variants by
name; provide pure-`Bool` versions, the extraction lifts them into `Result`.
-/

namespace core.cmp.impls

def PartialEqU8.eq    (x y : U8)    : Bool := x == y
def PartialEqU16.eq   (x y : U16)   : Bool := x == y
def PartialEqU32.eq   (x y : U32)   : Bool := x == y
def PartialEqU64.eq   (x y : U64)   : Bool := x == y
def PartialEqU128.eq  (x y : U128)  : Bool := x == y
def PartialEqUsize.eq (x y : Usize) : Bool := x == y
def PartialEqI8.eq    (x y : I8)    : Bool := x == y
def PartialEqI16.eq   (x y : I16)   : Bool := x == y
def PartialEqI32.eq   (x y : I32)   : Bool := x == y
def PartialEqI64.eq   (x y : I64)   : Bool := x == y
def PartialEqI128.eq  (x y : I128)  : Bool := x == y
def PartialEqIsize.eq (x y : Isize) : Bool := x == y

end core.cmp.impls
