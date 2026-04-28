/-
  Scalar trait instances for the Aeneas library.
  Imported after Types.lean which provides the trait structure definitions.
-/
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

end core

export Aeneas.Std (
  core.num.U8.MIN core.num.U8.MAX core.num.I8.MIN core.num.I8.MAX
  core.num.U16.MIN core.num.U16.MAX core.num.I16.MIN core.num.I16.MAX
  core.num.U32.MIN core.num.U32.MAX core.num.I32.MIN core.num.I32.MAX
  core.num.U64.MIN core.num.U64.MAX core.num.I64.MIN core.num.I64.MAX
  core.num.U128.MIN core.num.U128.MAX core.num.I128.MIN core.num.I128.MAX
  core.num.Usize.MIN core.num.Usize.MAX core.num.Isize.MIN core.num.Isize.MAX
)
