/-
  Scalar trait instances for the Aeneas library.
  Imported after Types.lean which provides the trait structure definitions.
-/
import CoreModels.Primitives
import CoreModels.Types

namespace core

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

-- /-! ## Array Clone / PartialEq

-- Aeneas extracts `<[T; N] as Clone>::clone` to `core.array.CloneArray.clone`
-- and `<[T; N] as PartialEq<[U; N]>>::eq` to
-- `core.array.equality.PartialEqArray.eq`. We provide trivial models that
-- satisfy the type signatures expected by extracted code. -/

-- namespace array

-- /-- Trivial model of array clone — returns the array unchanged. -/
-- def CloneArray.clone {T : Type} {N : Usize}
--     (_cloneInst : clone.Clone T) (a : Array T N) : Result (Array T N) := ok a

-- namespace equality

-- def PartialEqArray.eq {T U : Type} {N : Usize}
--     (partialEqInst : cmp.PartialEq T U) (a0 : Array T N) (a1 : Array U N) :
--     Result Bool := do
--   let rec loop : List T → List U → Result Bool
--     | [], []           => ok true
--     | x :: xs, y :: ys => do
--         let b ← partialEqInst.eq x y
--         if b then loop xs ys else ok false
--     | _, _             => ok false
--   loop a0.val a1.val

-- end equality

-- end array

-- /-! ## core::iter::range — Range iteration

-- Aeneas extracts `for i in lo..hi { … }` to a loop driven by
-- `core.iter.range.IteratorRange.next`, which in turn uses a
-- `core.iter.range.Step` dictionary. We provide both, plus a `StepUsize`
-- instance, so that downstream extracted code that iterates over `Range<usize>`
-- type-checks. -/

-- namespace iter.range

-- structure Step (Self : Type) where
--   cloneInst       : clone.Clone Self
--   partialOrdInst  : cmp.PartialOrd Self Self
--   steps_between   : Self → Self → Result (Usize × (Option Usize))
--   forward_checked : Self → Usize → Result (Option Self)
--   backward_checked: Self → Usize → Result (Option Self)

-- /-- Step instance for `Usize`. -/
-- def StepUsize : Step Usize := {
--   cloneInst       := clone.CloneUsize
--   partialOrdInst  := cmp.PartialOrdUsize
--   steps_between   := fun start «end» =>
--     if start.toNat > «end».toNat then ok (.ofNat 0, Option.none)
--     else
--       let s := .ofNat («end».toNat - start.toNat)
--       ok (s, Option.some s)
--   forward_checked := fun start n =>
--     let r := start.toNat + n.toNat
--     if r ≤ core.num.Usize.MAX.toNat then ok (Option.some (.ofNat r))
--     else ok Option.none
--   backward_checked := fun start n =>
--     if n.toNat ≤ start.toNat then ok (Option.some (.ofNat (start.toNat - n.toNat)))
--     else ok Option.none
-- }

-- /-- The `Iterator::next` implementation for `core::ops::range::Range<A>`,
--     parameterised over the `Step` dictionary. -/
-- def IteratorRange.next {A : Type} (StepInst : Step A) :
--     ops.range.Range A → Result ((Option A) × ops.range.Range A) := fun range => do
--   let cmp ← StepInst.partialOrdInst.partial_cmp range.start range.«end»
--   let isLess : Bool := match cmp with
--     | Option.some o => match o with
--                        | _root_.core.cmp.Ordering.Less => true
--                        | _ => false
--     | _ => false
--   if isLess then
--     let cur ← StepInst.cloneInst.clone range.start
--     let next? ← StepInst.forward_checked cur (.ofNat 1)
--     match next? with
--     | Option.none      => fail Error.panic
--     | Option.some next => ok (Option.some cur, { range with start := next })
--   else ok (Option.none, range)

-- end iter.range

end core
