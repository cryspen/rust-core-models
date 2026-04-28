/-
  Scalar trait instances for the Aeneas library.
  Imported after Types.lean which provides the trait structure definitions.
-/
import CoreModels.Types
import CoreModels.Alloc.Types

namespace CoreModels.core

open Aeneas.Std Result

/-! ## Scalar PartialEq / PartialOrd instances -/

private def liftBoolCmp2 {α β} (f : α → β → Bool) : α → β → Result Bool :=
  fun x y => ok (f x y)

def cmp.impls.PartialEqU8.eq    : U8    → U8    → Bool := (· == ·)
def cmp.impls.PartialEqU16.eq   : U16   → U16   → Bool := (· == ·)
def cmp.impls.PartialEqU32.eq   : U32   → U32   → Bool := (· == ·)
def cmp.impls.PartialEqU64.eq   : U64   → U64   → Bool := (· == ·)
def cmp.impls.PartialEqU128.eq  : U128  → U128  → Bool := (· == ·)
def cmp.impls.PartialEqUsize.eq : Usize → Usize → Bool := (· == ·)
def cmp.impls.PartialEqI8.eq    : I8    → I8    → Bool := (· == ·)
def cmp.impls.PartialEqI16.eq   : I16   → I16   → Bool := (· == ·)
def cmp.impls.PartialEqI32.eq   : I32   → I32   → Bool := (· == ·)
def cmp.impls.PartialEqI64.eq   : I64   → I64   → Bool := (· == ·)
def cmp.impls.PartialEqI128.eq  : I128  → I128  → Bool := (· == ·)
def cmp.impls.PartialEqIsize.eq : Isize → Isize → Bool := (· == ·)

def cmp.impls.PartialEqU8    : cmp.PartialEq U8    U8    := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqU16   : cmp.PartialEq U16   U16   := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqU32   : cmp.PartialEq U32   U32   := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqU64   : cmp.PartialEq U64   U64   := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqU128  : cmp.PartialEq U128  U128  := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqUsize : cmp.PartialEq Usize Usize := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqI8    : cmp.PartialEq I8    I8    := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqI16   : cmp.PartialEq I16   I16   := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqI32   : cmp.PartialEq I32   I32   := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqI64   : cmp.PartialEq I64   I64   := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqI128  : cmp.PartialEq I128  I128  := { eq := liftBoolCmp2 (· == ·) }
def cmp.impls.PartialEqIsize : cmp.PartialEq Isize Isize := { eq := liftBoolCmp2 (· == ·) }

private def mkUPartialOrd (ty) : cmp.PartialOrd (UScalar ty) (UScalar ty) := {
  PartialEqInst := { eq := liftBoolCmp2 (· == ·) }
  partial_cmp := fun x y =>
    ok (option.Option.Some
      (match compare x.val y.val with
       | .lt => cmp.Ordering.Less
       | .eq => cmp.Ordering.Equal
       | .gt => cmp.Ordering.Greater))
}

def cmp.PartialOrdU8    := mkUPartialOrd .U8
def cmp.PartialOrdU16   := mkUPartialOrd .U16
def cmp.PartialOrdU32   := mkUPartialOrd .U32
def cmp.PartialOrdU64   := mkUPartialOrd .U64
def cmp.PartialOrdU128  := mkUPartialOrd .U128
def cmp.PartialOrdUsize := mkUPartialOrd .Usize

private def mkIPartialOrd (ty) : cmp.PartialOrd (IScalar ty) (IScalar ty) := {
  PartialEqInst := { eq := liftBoolCmp2 (· == ·) }
  partial_cmp := fun x y =>
    ok (option.Option.Some
      (match compare x.val y.val with
       | .lt => cmp.Ordering.Less
       | .eq => cmp.Ordering.Equal
       | .gt => cmp.Ordering.Greater))
}

def cmp.PartialOrdI8    := mkIPartialOrd .I8
def cmp.PartialOrdI16   := mkIPartialOrd .I16
def cmp.PartialOrdI32   := mkIPartialOrd .I32
def cmp.PartialOrdI64   := mkIPartialOrd .I64
def cmp.PartialOrdI128  := mkIPartialOrd .I128
def cmp.PartialOrdIsize := mkIPartialOrd .Isize

end CoreModels.core

namespace CoreModels
namespace core

/-! ### Scalar Clone / Copy instances

Aeneas's standard library names them `core.clone.CloneU8`, `core.marker.CopyU8`,
etc. Downstream Aeneas-extracted code that calls e.g. `<u64 as Clone>::clone`
references these exact names. -/

private def builtinScalarClone {α : Type} : clone.Clone α where
  clone := fun x => Aeneas.Std.Result.ok x

def clone.CloneU8    : clone.Clone U8    := builtinScalarClone
def clone.CloneU16   : clone.Clone U16   := builtinScalarClone
def clone.CloneU32   : clone.Clone U32   := builtinScalarClone
def clone.CloneU64   : clone.Clone U64   := builtinScalarClone
def clone.CloneU128  : clone.Clone U128  := builtinScalarClone
def clone.CloneUsize : clone.Clone Usize := builtinScalarClone
def clone.CloneI8    : clone.Clone I8    := builtinScalarClone
def clone.CloneI16   : clone.Clone I16   := builtinScalarClone
def clone.CloneI32   : clone.Clone I32   := builtinScalarClone
def clone.CloneI64   : clone.Clone I64   := builtinScalarClone
def clone.CloneI128  : clone.Clone I128  := builtinScalarClone
def clone.CloneIsize : clone.Clone Isize := builtinScalarClone
def clone.CloneBool  : clone.Clone Bool  := builtinScalarClone

def marker.CopyU8    : marker.Copy U8    := { cloneInst := clone.CloneU8 }
def marker.CopyU16   : marker.Copy U16   := { cloneInst := clone.CloneU16 }
def marker.CopyU32   : marker.Copy U32   := { cloneInst := clone.CloneU32 }
def marker.CopyU64   : marker.Copy U64   := { cloneInst := clone.CloneU64 }
def marker.CopyU128  : marker.Copy U128  := { cloneInst := clone.CloneU128 }
def marker.CopyUsize : marker.Copy Usize := { cloneInst := clone.CloneUsize }
def marker.CopyI8    : marker.Copy I8    := { cloneInst := clone.CloneI8 }
def marker.CopyI16   : marker.Copy I16   := { cloneInst := clone.CloneI16 }
def marker.CopyI32   : marker.Copy I32   := { cloneInst := clone.CloneI32 }
def marker.CopyI64   : marker.Copy I64   := { cloneInst := clone.CloneI64 }
def marker.CopyI128  : marker.Copy I128  := { cloneInst := clone.CloneI128 }
def marker.CopyIsize : marker.Copy Isize := { cloneInst := clone.CloneIsize }
def marker.CopyBool  : marker.Copy Bool  := { cloneInst := clone.CloneBool }

/-! ### Pure scalar Clone helpers

Aeneas extracts `<u8 as Clone>::clone` to a *pure* function
`core.clone.impls.CloneU8.clone` (Aeneas marks it `~can_fail:false`).
The implementation is just the identity. -/

namespace clone.impls

def CloneU8.clone    (x : U8)    : U8    := x
def CloneU16.clone   (x : U16)   : U16   := x
def CloneU32.clone   (x : U32)   : U32   := x
def CloneU64.clone   (x : U64)   : U64   := x
def CloneU128.clone  (x : U128)  : U128  := x
def CloneUsize.clone (x : Usize) : Usize := x
def CloneI8.clone    (x : I8)    : I8    := x
def CloneI16.clone   (x : I16)   : I16   := x
def CloneI32.clone   (x : I32)   : I32   := x
def CloneI64.clone   (x : I64)   : I64   := x
def CloneI128.clone  (x : I128)  : I128  := x
def CloneIsize.clone (x : Isize) : Isize := x
def CloneBool.clone  (x : Bool)  : Bool  := x

end clone.impls

/-! ## core::iter::range — Range iteration

Aeneas extracts `for i in lo..hi { … }` to a loop driven by
`core.iter.range.IteratorRange.next`, which in turn uses a
`core.iter.range.Step` dictionary. We provide both, plus a `StepUsize`
instance, so that downstream extracted code that iterates over `Range<usize>`
type-checks. -/

namespace iter.range

structure Step (Self : Type) where
  cloneInst       : clone.Clone Self
  partialOrdInst  : cmp.PartialOrd Self Self
  steps_between   : Self → Self → Aeneas.Std.Result (Aeneas.Std.Usize × (Option Aeneas.Std.Usize))
  forward_checked : Self → Aeneas.Std.Usize → Aeneas.Std.Result (Option Self)
  backward_checked: Self → Aeneas.Std.Usize → Aeneas.Std.Result (Option Self)

/-- Step instance for `Usize`. -/
def StepUsize : Step Aeneas.Std.Usize := {
  cloneInst       := clone.CloneUsize
  partialOrdInst  := cmp.PartialOrdUsize
  steps_between   := Aeneas.Std.core.iter.range.StepUsize.steps_between
  forward_checked := Aeneas.Std.core.iter.range.StepUsize.forward_checked
  backward_checked := Aeneas.Std.core.iter.range.StepUsize.backward_checked
}

/-- The `Iterator::next` implementation for `core::ops::range::Range<A>`,
    parameterised over the `Step` dictionary. -/
def IteratorRange.next {A : Type} (StepInst : Step A) :
    ops.range.Range A → Aeneas.Std.Result ((Option A) × ops.range.Range A) := fun range => do
  let cmp ← StepInst.partialOrdInst.partial_cmp range.start range.«end»
  let isLess : Bool := match cmp with
    | Option.some o => match o with
                       | CoreModels.core.cmp.Ordering.Less => true
                       | _ => false
    | _ => false
  if isLess then
    let cur ← StepInst.cloneInst.clone range.start
    let next? ← StepInst.forward_checked cur 1#usize
    match next? with
    | Option.none      => .fail .panic
    | Option.some next => .ok (Option.some cur, { range with start := next })
  else .ok (Option.none, range)

end iter.range

end core

/-! ## Redirects to Aeneas's library -/

export Aeneas.Std (
  core.num.U8.MIN core.num.U8.MAX core.num.I8.MIN core.num.I8.MAX
  core.num.U16.MIN core.num.U16.MAX core.num.I16.MIN core.num.I16.MAX
  core.num.U32.MIN core.num.U32.MAX core.num.I32.MIN core.num.I32.MAX
  core.num.U64.MIN core.num.U64.MAX core.num.I64.MIN core.num.I64.MAX
  core.num.U128.MIN core.num.U128.MAX core.num.I128.MIN core.num.I128.MAX
  core.num.Usize.MIN core.num.Usize.MAX core.num.Isize.MIN core.num.Isize.MAX
  core.num.U8.wrapping_add core.num.I8.wrapping_add
  core.num.U16.wrapping_add core.num.I16.wrapping_add
  core.num.U32.wrapping_add core.num.I32.wrapping_add
  core.num.U64.wrapping_add core.num.I64.wrapping_add
  core.num.U128.wrapping_add core.num.I128.wrapping_add
  core.num.Usize.wrapping_add core.num.Isize.wrapping_add
  core.num.U8.wrapping_sub core.num.I8.wrapping_sub
  core.num.U16.wrapping_sub core.num.I16.wrapping_sub
  core.num.U32.wrapping_sub core.num.I32.wrapping_sub
  core.num.U64.wrapping_sub core.num.I64.wrapping_sub
  core.num.U128.wrapping_sub core.num.I128.wrapping_sub
  core.num.Usize.wrapping_sub core.num.Isize.wrapping_sub
  core.num.U8.wrapping_mul core.num.I8.wrapping_mul
  core.num.U16.wrapping_mul core.num.I16.wrapping_mul
  core.num.U32.wrapping_mul core.num.I32.wrapping_mul
  core.num.U64.wrapping_mul core.num.I64.wrapping_mul
  core.num.U128.wrapping_mul core.num.I128.wrapping_mul
  core.num.Usize.wrapping_mul core.num.Isize.wrapping_mul
  core.option.Option.unwrap_or
  core.option.Option.is_some
  core.option.Option.is_none
  core.option.Option.take
  core.mem.swap core.mem.replace
)

end CoreModels
