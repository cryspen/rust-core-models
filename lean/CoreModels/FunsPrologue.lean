/-
  Scalar trait instances for the Aeneas library.
  Imported after Types.lean which provides the trait structure definitions.
-/
import CoreModels.Types
import CoreModels.Alloc.Types

namespace core_models

open Aeneas.Std Result

/-! ## Scalar PartialEq / PartialOrd instances -/

private def liftBoolCmp2 {α β} (f : α → β → Bool) : α → β → Result Bool :=
  fun x y => ok (f x y)

instance U8.Insts.Core_modelsCmpPartialEqU8       : cmp.PartialEq U8    U8    := { eq := liftBoolCmp2 (· == ·) }
instance U16.Insts.Core_modelsCmpPartialEqU16     : cmp.PartialEq U16   U16   := { eq := liftBoolCmp2 (· == ·) }
instance U32.Insts.Core_modelsCmpPartialEqU32     : cmp.PartialEq U32   U32   := { eq := liftBoolCmp2 (· == ·) }
instance U64.Insts.Core_modelsCmpPartialEqU64     : cmp.PartialEq U64   U64   := { eq := liftBoolCmp2 (· == ·) }
instance U128.Insts.Core_modelsCmpPartialEqU128   : cmp.PartialEq U128  U128  := { eq := liftBoolCmp2 (· == ·) }
instance Usize.Insts.Core_modelsCmpPartialEqUsize : cmp.PartialEq Usize Usize := { eq := liftBoolCmp2 (· == ·) }
instance I8.Insts.Core_modelsCmpPartialEqI8       : cmp.PartialEq I8    I8    := { eq := liftBoolCmp2 (· == ·) }
instance I16.Insts.Core_modelsCmpPartialEqI16     : cmp.PartialEq I16   I16   := { eq := liftBoolCmp2 (· == ·) }
instance I32.Insts.Core_modelsCmpPartialEqI32     : cmp.PartialEq I32   I32   := { eq := liftBoolCmp2 (· == ·) }
instance I64.Insts.Core_modelsCmpPartialEqI64     : cmp.PartialEq I64   I64   := { eq := liftBoolCmp2 (· == ·) }
instance I128.Insts.Core_modelsCmpPartialEqI128   : cmp.PartialEq I128  I128  := { eq := liftBoolCmp2 (· == ·) }
instance Isize.Insts.Core_modelsCmpPartialEqIsize : cmp.PartialEq Isize Isize := { eq := liftBoolCmp2 (· == ·) }

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
                       | core_models.cmp.Ordering.Less => true
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

abbrev ops.range.Range.Insts.Core_modelsIterTraitsIteratorIterator.next :=
  @core_models.iter.range.IteratorRange.next

abbrev Usize.Insts.Core_modelsIterRangeStep := core_models.iter.range.StepUsize

/-! ## Slice -/

def slice.Slice.len {T : Type u} (v : Aeneas.Std.Slice T) : Aeneas.Std.Result Usize :=
  pure (@Aeneas.Std.Slice.len T v)

/-! ## Option -/

def option.Option.unwrap_or :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.unwrap_or T x y)

def option.Option.is_some :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_some T x)

def option.Option.is_none :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.is_none T x)

def option.Option.take :=
  fun {T} x => Aeneas.Std.Result.ok (@Aeneas.Std.core.option.Option.take T x)

/-! ## Mem -/

def mem.swap :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.swap T x y)

def mem.replace :=
  fun {T} x y => Aeneas.Std.Result.ok (@Aeneas.Std.core.mem.replace T x y)

/-! ## Redirects to Aeneas's library -/

export Aeneas.Std.core (
  num.U8.MIN num.U8.MAX num.I8.MIN num.I8.MAX
  num.U16.MIN num.U16.MAX num.I16.MIN num.I16.MAX
  num.U32.MIN num.U32.MAX num.I32.MIN num.I32.MAX
  num.U64.MIN num.U64.MAX num.I64.MIN num.I64.MAX
  num.U128.MIN num.U128.MAX num.I128.MIN num.I128.MAX
  num.Usize.MIN num.Usize.MAX num.Isize.MIN num.Isize.MAX
  convert.num.FromU16U8.from
  convert.num.FromU32U8.from
  convert.num.FromU32U16.from
  convert.num.FromU64U8.from
  convert.num.FromU64U16.from
  convert.num.FromU64U32.from
  convert.num.FromU128U8.from
  convert.num.FromU128U16.from
  convert.num.FromU128U32.from
  convert.num.FromU128U64.from
  convert.num.FromUsizeU8.from
  convert.num.FromUsizeU16.from
  convert.num.FromI16I8.from
  convert.num.FromI32I8.from
  convert.num.FromI32I16.from
  convert.num.FromI64I8.from
  convert.num.FromI64I16.from
  convert.num.FromI64I32.from
  convert.num.FromI128I8.from
  convert.num.FromI128I16.from
  convert.num.FromI128I32.from
  convert.num.FromI128I64.from
  convert.num.FromIsizeI8.from
  convert.num.FromIsizeI16.from
)

end core_models
