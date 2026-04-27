import Aeneas.MissingLean
import Aeneas.USize64
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.SInt

/-!
# ISize64

We define a type `ISize64` to represent Rust's `isize` type. It is simply a copy of `Int64`.
This file aims to collect all definitions, lemmas, and type class instances about `Int64` from
Lean's standard library and to state them for `ISize64`.

The regular `ISize` type does not work for us because of https://github.com/cryspen/hax/issues/1702.

## Source references

All definitions, lemmas, instances, and simp procedures in this file are adapted from the
following files in the Lean v4.29.0-rc1 source code:
- `Init/Data/SInt/Basic.lean` (structure, basic defs, arithmetic, conversions)
- `Init/Data/SInt/Lemmas.lean` (all lemmas and instances)
- `Init/GrindInstances/ToInt.lean` (Grind ToInt instances)
- `Init/GrindInstances/Ring/SInt.lean` (CommRing, IsCharP, ToInt.Pow)
- `Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean` (simp procedures)
-/

-- Adapted from Init/Data/SInt/Basic.lean (Lean v4.29.0-rc1)

/-- A copy of `Int64`, which we use to represent Rust's `isize` type. -/
structure ISize64 where
  ofUSize64 ::
  toUSize64 : USize64

@[inline] def ISize64.toBitVec (x : ISize64) : BitVec 64 := x.toUSize64.toBitVec
def ISize64.ofBitVec (b : BitVec 64) : ISize64 := ⟨⟨b⟩⟩

/-- The number of distinct values representable by `ISize64`, that is, `2^64 = 18446744073709551616`. -/
@[reducible] def ISize64.size : Nat := Int64.size

theorem ISize64.toBitVec.inj : {x y : ISize64} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Converts an arbitrary-precision integer to `ISize64`, wrapping on overflow or underflow. -/
def ISize64.ofInt (i : @& Int) : ISize64 := ⟨⟨BitVec.ofInt 64 i⟩⟩

/-- Converts a natural number to `ISize64`, wrapping around to negative numbers on overflow. -/
def ISize64.ofNat (n : @& Nat) : ISize64 := ⟨⟨BitVec.ofNat 64 n⟩⟩

abbrev Int.toISize64 := ISize64.ofInt

abbrev Nat.toISize64 := ISize64.ofNat

/-- Converts an `ISize64` to an arbitrary-precision integer that denotes the same number. -/
def ISize64.toInt (i : ISize64) : Int := i.toBitVec.toInt

/-- Converts an `ISize64` to a natural number, mapping all negative numbers to `0`. -/
@[suggest_for ISize64.toNat, inline] def ISize64.toNatClampNeg (i : ISize64) : Nat := i.toInt.toNat

/-- Converts an `ISize64` to an 8-bit signed integer by truncating its bitvector representation. -/
def ISize64.toInt8 (a : ISize64) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩

/-- Converts an `ISize64` to a 16-bit signed integer by truncating its bitvector representation. -/
def ISize64.toInt16 (a : ISize64) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩

/-- Converts an `ISize64` to a 32-bit signed integer by truncating its bitvector representation. -/
def ISize64.toInt32 (a : ISize64) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩

/-- Converts an `ISize64` to a 64-bit signed integer. -/
def ISize64.toInt64 (a : ISize64) : Int64 := ⟨⟨a.toBitVec⟩⟩

/-- Converts an `ISize64` to a word-sized signed integer. -/
def ISize64.toISize (a : ISize64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩

/-- Converts an 8-bit signed integer to `ISize64`. -/
def Int8.toISize64 (a : Int8) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

/-- Converts a 16-bit signed integer to `ISize64`. -/
def Int16.toISize64 (a : Int16) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

/-- Converts a 32-bit signed integer to `ISize64`. -/
def Int32.toISize64 (a : Int32) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

/-- Converts a 64-bit signed integer to `ISize64`. -/
def Int64.toISize64 (a : Int64) : ISize64 := ⟨⟨a.toBitVec⟩⟩

/-- Converts a word-sized signed integer to `ISize64`. -/
def ISize.toISize64 (a : ISize) : ISize64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩

/-- Negates an `ISize64`. Usually accessed via the `-` prefix operator. -/
def ISize64.neg (i : ISize64) : ISize64 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString ISize64 where
  toString i := toString i.toInt
instance : Repr ISize64 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom ISize64 := ⟨⟩

instance : Hashable ISize64 where
  hash i := UInt64.ofInt i.toInt

instance ISize64.instOfNat {n} : OfNat ISize64 n := ⟨ISize64.ofNat n⟩
instance ISize64.instNeg : Neg ISize64 where
  neg := ISize64.neg

/-- The largest number that `ISize64` can represent: `2^63 - 1 = 9223372036854775807`. -/
abbrev ISize64.maxValue : ISize64 := 9223372036854775807

/-- The smallest number that `ISize64` can represent: `-2^63 = -9223372036854775808`. -/
abbrev ISize64.minValue : ISize64 := -9223372036854775808

/-- Constructs an `ISize64` from an `Int` that is known to be in bounds. -/
@[inline]
def ISize64.ofIntLE (i : Int) (_hl : ISize64.minValue.toInt ≤ i) (_hr : i ≤ ISize64.maxValue.toInt) : ISize64 :=
  ISize64.ofInt i

/-- Constructs an `ISize64` from an `Int`, clamping if the value is too small or too large. -/
def ISize64.ofIntTruncate (i : Int) : ISize64 :=
  if hl : ISize64.minValue.toInt ≤ i then
    if hr : i ≤ ISize64.maxValue.toInt then
      ISize64.ofIntLE i hl hr
    else
      ISize64.minValue
  else
    ISize64.minValue

protected def ISize64.add (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
protected def ISize64.sub (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
protected def ISize64.mul (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
protected def ISize64.div (a b : ISize64) : ISize64 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
protected def ISize64.pow (x : ISize64) (n : Nat) : ISize64 :=
  match n with
  | 0 => 1
  | n + 1 => ISize64.mul (ISize64.pow x n) x
protected def ISize64.mod (a b : ISize64) : ISize64 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩

protected def ISize64.land (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
protected def ISize64.lor (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
protected def ISize64.xor (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
protected def ISize64.shiftLeft (a b : ISize64) : ISize64 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 64)⟩⟩
protected def ISize64.shiftRight (a b : ISize64) : ISize64 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)⟩⟩
protected def ISize64.complement (a : ISize64) : ISize64 := ⟨⟨~~~a.toBitVec⟩⟩
protected def ISize64.abs (a : ISize64) : ISize64 := ⟨⟨a.toBitVec.abs⟩⟩

def ISize64.decEq (a b : ISize64) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => ISize64.noConfusion h' (fun h' => absurd h' h)))

protected def ISize64.lt (a b : ISize64) : Prop := a.toBitVec.slt b.toBitVec
protected def ISize64.le (a b : ISize64) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited ISize64 where
  default := 0

instance : Add ISize64         := ⟨ISize64.add⟩
instance : Sub ISize64         := ⟨ISize64.sub⟩
instance : Mul ISize64         := ⟨ISize64.mul⟩
instance : Pow ISize64 Nat     := ⟨ISize64.pow⟩
instance : Mod ISize64         := ⟨ISize64.mod⟩
instance : Div ISize64         := ⟨ISize64.div⟩
instance : LT ISize64          := ⟨ISize64.lt⟩
instance : LE ISize64          := ⟨ISize64.le⟩
instance : Complement ISize64  := ⟨ISize64.complement⟩
instance : AndOp ISize64       := ⟨ISize64.land⟩
instance : OrOp ISize64        := ⟨ISize64.lor⟩
instance : XorOp ISize64         := ⟨ISize64.xor⟩
instance : ShiftLeft ISize64   := ⟨ISize64.shiftLeft⟩
instance : ShiftRight ISize64  := ⟨ISize64.shiftRight⟩
instance : DecidableEq ISize64 := ISize64.decEq

/-- Converts `true` to `1` and `false` to `0`. -/
def Bool.toISize64 (b : Bool) : ISize64 := if b then 1 else 0

def ISize64.decLt (a b : ISize64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

def ISize64.decLe (a b : ISize64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

attribute [instance_reducible, instance] ISize64.decLt ISize64.decLe

instance : Max ISize64 := maxOfLe
instance : Min ISize64 := minOfLe

/-- Converts an `ISize64` to a `UInt8`. -/
def ISize64.toUInt8 (a : ISize64) : UInt8 := a.toNatClampNeg.toUInt8

/-- Converts an `ISize64` to a `UInt16`. -/
def ISize64.toUInt16 (a : ISize64) : UInt16 := a.toNatClampNeg.toUInt16

/-- Converts an `ISize64` to a `UInt32`. -/
def ISize64.toUInt32 (a : ISize64) : UInt32 := a.toNatClampNeg.toUInt32

/-- Converts an `ISize64` to a `UInt64`. -/
def ISize64.toUInt64 (a : ISize64) : UInt64 := ⟨a.toBitVec⟩

/-- Converts an `ISize64` to a `USize`. -/
def ISize64.toUSize (a : ISize64) : USize := a.toNatClampNeg.toUSize

/-- Converts a `UInt8` to `ISize64`. -/
def UInt8.toISize64 (a : UInt8) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `UInt16` to `ISize64`. -/
def UInt16.toISize64 (a : UInt16) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `UInt32` to `ISize64`. -/
def UInt32.toISize64 (a : UInt32) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `UInt64` to `ISize64`. -/
def UInt64.toISize64 (a : UInt64) : ISize64 := ⟨⟨a.toBitVec⟩⟩

/-- Converts a `USize` to `ISize64`. -/
def USize.toISize64 (a : USize) : ISize64 := ISize64.ofInt a.toNat

/-- Converts a `USize64` to `ISize64`. -/
def USize64.toISize64 (a : USize64) : ISize64 := ⟨a⟩

/-!
## Theorems from `declare_int_theorems`

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), line 31–61.
-/

open Std Lean in
set_option autoImplicit true in
declare_int_theorems ISize64 64

/-!
## Lemmas from `Init.Data.SInt.Lemmas` (up to line 725)

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 75–725.
-/

theorem ISize64.toInt.inj {x y : ISize64} (h : x.toInt = y.toInt) : x = y :=
  ISize64.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem ISize64.toInt_inj {x y : ISize64} : x.toInt = y.toInt ↔ x = y :=
  ⟨ISize64.toInt.inj, fun h => h ▸ rfl⟩

@[simp, int_toBitVec] theorem ISize64.toBitVec_neg (x : ISize64) : (-x).toBitVec = -x.toBitVec := (rfl)

@[simp] theorem ISize64.toBitVec_zero : toBitVec 0 = 0#64 := (rfl)

theorem ISize64.toBitVec_one : (1 : ISize64).toBitVec = 1#64 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)

@[simp] protected theorem ISize64.neg_zero : -(0 : ISize64) = 0 := (rfl)

@[simp] theorem ISize64.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod ISize64.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]

@[simp] theorem ISize64.toInt_ofNat' {n : Nat} : toInt (ofNat n) = (n : Int).bmod ISize64.size := by
  rw [toInt, toBitVec_ofNat', BitVec.toInt_ofNat']

theorem ISize64.toInt_ofNat {n : Nat} : toInt (no_index (OfNat.ofNat n)) = (n : Int).bmod ISize64.size := by
  rw [toInt, toBitVec_ofNat, BitVec.toInt_ofNat]

theorem ISize64.toInt_ofInt_of_le {n : Int} (hn : -2^63 ≤ n) (hn' : n < 2^63) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']

theorem ISize64.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem ISize64.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)

theorem ISize64.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem ISize64.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]

theorem ISize64.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]

theorem ISize64.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2^63) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt_of_le (by omega) (by omega)]

theorem ISize64.toInt_zero : toInt 0 = 0 := by
  rw [toInt_ofNat, ISize64.size]; decide

theorem ISize64.toInt_minValue : ISize64.minValue.toInt = -2^63 := (rfl)

theorem ISize64.toInt_maxValue : ISize64.maxValue.toInt = 2 ^ 63 - 1 := (rfl)

@[simp] theorem ISize64.toNatClampNeg_minValue : ISize64.minValue.toNatClampNeg = 0 := (rfl)

@[simp] theorem ISize64.toNat_toInt (x : ISize64) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem ISize64.toInt_toBitVec (x : ISize64) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt8 (x : ISize64) :
    x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt16 (x : ISize64) :
    x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt32 (x : ISize64) :
    x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toInt64 (x : ISize64) :
    x.toInt64.toBitVec = x.toBitVec := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_toISize (x : ISize64) :
    x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

theorem ISize64.toInt_lt (x : ISize64) : x.toInt < 2 ^ 63 :=
  Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)

theorem ISize64.le_toInt (x : ISize64) : -2 ^ 63 ≤ x.toInt :=
  Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)

theorem ISize64.toInt_le (x : ISize64) : x.toInt ≤ ISize64.maxValue.toInt :=
  Int.le_of_lt_add_one x.toInt_lt

theorem ISize64.minValue_le_toInt (x : ISize64) : ISize64.minValue.toInt ≤ x.toInt := x.le_toInt

theorem ISize64.toNatClampNeg_lt (x : ISize64) : x.toNatClampNeg < 2 ^ 63 :=
  (Int.toNat_lt' (by decide)).2 x.toInt_lt

@[simp] theorem ISize64.toInt_toInt8 (x : ISize64) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem ISize64.toInt_toInt16 (x : ISize64) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem ISize64.toInt_toInt32 (x : ISize64) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem ISize64.toInt_toInt64 (x : ISize64) : x.toInt64.toInt = x.toInt := (rfl)
@[simp] theorem ISize64.toInt_toISize (x : ISize64) :
    x.toISize.toInt = x.toInt.bmod (2 ^ System.Platform.numBits) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem ISize64.ofBitVec_toBitVec (x : ISize64) : ISize64.ofBitVec x.toBitVec = x := (rfl)

@[simp] theorem ISize64.ofBitVec_int8ToBitVec (x : Int8) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_int16ToBitVec (x : Int16) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_int32ToBitVec (x : Int32) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_int64ToBitVec (x : Int64) :
    ISize64.ofBitVec x.toBitVec = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofBitVec_iSizeToBitVec (x : ISize) :
    ISize64.ofBitVec (x.toBitVec.signExtend 64) = x.toISize64 := (rfl)

@[simp] theorem ISize64.toBitVec_ofIntLE (x : Int) (h₁ h₂) :
    (ISize64.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 64 x := (rfl)

@[simp] theorem ISize64.toInt_bmod (x : ISize64) :
    x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le x.le_toInt x.toInt_lt

-- Alias used by simp in other contexts
@[simp] theorem ISize64.toInt_bmod_size (x : ISize64) :
    x.toInt.bmod ISize64.size = x.toInt :=
  ISize64.toInt_bmod x

@[simp] theorem BitVec.ofInt_iSize64ToInt (x : ISize64) :
    BitVec.ofInt 64 x.toInt = x.toBitVec :=
  BitVec.eq_of_toInt_eq (by simp)

@[simp] theorem ISize64.ofIntLE_toInt (x : ISize64) :
    ISize64.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x :=
  ISize64.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofInt_toInt (x : ISize64) : ISize64.ofInt x.toInt = x :=
  ISize64.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofInt_int8ToInt (x : Int8) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofInt_int16ToInt (x : Int16) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofInt_int32ToInt (x : Int32) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofInt_int64ToInt (x : Int64) : ISize64.ofInt x.toInt = x.toISize64 := by
  show ISize64.ofBitVec (BitVec.ofInt 64 x.toBitVec.toInt) = ⟨⟨x.toBitVec⟩⟩
  congr 1; exact BitVec.ofInt_toInt ..
@[simp] theorem ISize64.ofInt_iSizeToInt (x : ISize) : ISize64.ofInt x.toInt = x.toISize64 := (rfl)

@[simp] theorem ISize64.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

theorem ISize64.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} :
    (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]

theorem ISize64.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : ISize64.ofIntLE n h₁ h₂ = ISize64.ofInt n := (rfl)

theorem ISize64.toInt_ofIntTruncate {x : Int} (h₁ : ISize64.minValue.toInt ≤ x)
    (h₂ : x ≤ ISize64.maxValue.toInt) : (ISize64.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]

@[simp] theorem ISize64.ofIntTruncate_toInt (x : ISize64) : ISize64.ofIntTruncate x.toInt = x :=
  ISize64.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)

theorem ISize64.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : ISize64) :
    ISize64.ofInt a = b ↔ a.bmod (2 ^ 64) = b.toInt := by
  simp [← ISize64.toInt_inj]

/-!
## More lemmas from `Init.Data.SInt.Lemmas` (lines 725–1000)

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 725–1000.
-/

-- Cross-type toInt lemmas needed below
@[simp] theorem Int8.toInt_toISize64 (x : Int8) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int16.toInt_toISize64 (x : Int16) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int32.toInt_toISize64 (x : Int32) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int64.toInt_toISize64 (x : Int64) : x.toISize64.toInt = x.toInt := (rfl)
@[simp] theorem ISize.toInt_toISize64 (x : ISize) : x.toISize64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem ISize64.ofIntTruncate_int8ToInt (x : Int8) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toISize64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize64.ofIntTruncate_int16ToInt (x : Int16) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toISize64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize64.ofIntTruncate_int32ToInt (x : Int32) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int32.toInt_toISize64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))

@[simp] theorem ISize64.ofIntTruncate_int64ToInt (x : Int64) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int64.toInt_toISize64]
    · exact x.minValue_le_toInt
    · exact x.toInt_le)

@[simp] theorem ISize64.ofIntTruncate_iSizeToInt (x : ISize) : ISize64.ofIntTruncate x.toInt = x.toISize64 :=
  ISize64.toInt.inj (by
    rw [toInt_ofIntTruncate, ISize.toInt_toISize64]
    · exact Int.le_trans (by decide) x.le_toInt
    · exact Int.le_of_lt_add_one x.toInt_lt)

theorem ISize64.le_iff_toInt_le {x y : ISize64} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le

theorem ISize64.lt_iff_toInt_lt {x y : ISize64} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt

theorem ISize64.cast_toNatClampNeg (x : ISize64) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]

theorem ISize64.ofNat_toNatClampNeg (x : ISize64) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])

theorem ISize64.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x.toISize64 :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toISize64])

theorem ISize64.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x.toISize64 :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toISize64])

theorem ISize64.ofNat_int32ToNatClampNeg (x : Int32) (hx : 0 ≤ x) : ISize64.ofNat x.toNatClampNeg = x.toISize64 :=
  ISize64.toInt.inj (by rw [ISize64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int32.cast_toNatClampNeg _ hx, Int32.toInt_toISize64])

@[simp] theorem ISize64.toInt8_toInt16 (n : ISize64) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize64.toInt8_toInt32 (n : ISize64) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize64.toInt8_toISize (n : ISize64) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize64.toInt16_toInt32 (n : ISize64) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize64.toInt16_toISize (n : ISize64) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize64.toInt32_toISize (n : ISize64) : n.toISize.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp, int_toBitVec] theorem ISize64.toBitVec_ofBitVec' (b) : (ISize64.ofBitVec b).toBitVec = b := (rfl)

/-!
## More lemmas from `Init.Data.SInt.Lemmas` (lines 1000–1840)

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 1000–1840.
-/

theorem ISize64.toBitVec_ofIntTruncate {n : Int} (h₁ : ISize64.minValue.toInt ≤ n) (h₂ : n ≤ ISize64.maxValue.toInt) :
    (ISize64.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]

@[simp] theorem ISize64.toInt_ofBitVec (b) : (ISize64.ofBitVec b).toInt = b.toInt := (rfl)

@[simp] theorem ISize64.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) :
    (ISize64.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]

@[simp] theorem ISize64.toNatClampNeg_ofBitVec (b) :
    (ISize64.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)

theorem ISize64.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]

theorem ISize64.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega

@[simp] theorem ISize64.toUInt64_ofBitVec (b) :
    (ISize64.ofBitVec b).toUInt64 = UInt64.ofBitVec b := (rfl)

theorem ISize64.toInt8_ofIntLE {n} (h₁ h₂) :
    (ISize64.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)
@[simp] theorem ISize64.toInt8_ofBitVec (b) :
    (ISize64.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize64.toInt8_ofNat' {n} : (ISize64.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem ISize64.toInt8_ofInt {n} : (ISize64.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize64.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'
theorem ISize64.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]

theorem ISize64.toInt16_ofIntLE {n} (h₁ h₂) :
    (ISize64.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)
@[simp] theorem ISize64.toInt16_ofBitVec (b) :
    (ISize64.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize64.toInt16_ofNat' {n} : (ISize64.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem ISize64.toInt16_ofInt {n} : (ISize64.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize64.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'
theorem ISize64.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]

theorem ISize64.toInt32_ofIntLE {n} (h₁ h₂) :
    (ISize64.ofIntLE n h₁ h₂).toInt32 = Int32.ofInt n := Int32.toInt.inj (by simp)
@[simp] theorem ISize64.toInt32_ofBitVec (b) :
    (ISize64.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize64.toInt32_ofNat' {n} : (ISize64.ofNat n).toInt32 = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem ISize64.toInt32_ofInt {n} : (ISize64.ofInt n).toInt32 = Int32.ofInt n :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize64.toInt32_ofNat {n} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt32_ofNat'
theorem ISize64.toInt32_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toInt32 = Int32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt32_ofIntLE]

@[simp] theorem ISize64.toISize_ofBitVec (b) :
    (ISize64.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize64.toISize_ofInt {n} : (ISize64.ofInt n).toISize = ISize.ofInt n := by
  apply ISize.toInt.inj
  simp only [toInt_toISize, toInt_ofInt, ISize.toInt_ofInt, ISize64.size]
  apply Int.bmod_bmod_of_dvd
  cases System.Platform.numBits_eq <;> simp_all <;> decide
theorem ISize64.toISize_ofIntLE {n} (h₁ h₂) :
    (ISize64.ofIntLE n h₁ h₂).toISize = ISize.ofInt n := by
  rw [ofIntLE, toISize_ofInt]
@[simp] theorem ISize64.toISize_ofNat' {n} : (ISize64.ofNat n).toISize = ISize.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize_ofInt, ISize.ofInt_eq_ofNat]
@[simp] theorem ISize64.toISize_ofNat {n} : toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize_ofNat'
theorem ISize64.toISize_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (ISize64.ofIntTruncate n).toISize = ISize.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toISize_ofIntLE]

@[simp, int_toBitVec] theorem ISize64.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)
@[simp, int_toBitVec] theorem ISize64.toBitVec_maxValue : maxValue.toBitVec = BitVec.intMax _ := (rfl)

@[simp] theorem ISize64.toInt8_neg (x : ISize64) : (-x).toInt8 = -x.toInt8 :=
  Int8.toBitVec.inj (by simp)
@[simp] theorem ISize64.toInt16_neg (x : ISize64) : (-x).toInt16 = -x.toInt16 :=
  Int16.toBitVec.inj (by simp)
@[simp] theorem ISize64.toInt32_neg (x : ISize64) : (-x).toInt32 = -x.toInt32 :=
  Int32.toBitVec.inj (by simp)
@[simp] theorem ISize64.toISize_neg (x : ISize64) : (-x).toISize = -x.toISize :=
  ISize.toBitVec.inj (by simp)

@[simp] theorem ISize64.ofIntLE_bitVecToInt (n : BitVec 64) :
    ISize64.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp)
theorem ISize64.ofBitVec_ofNatLT (n : Nat) (hn) :
    ISize64.ofBitVec (BitVec.ofNatLT n hn) = ISize64.ofNat n :=
  ISize64.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])
@[simp] theorem ISize64.ofBitVec_ofNat (n : Nat) :
    ISize64.ofBitVec (BitVec.ofNat 64 n) = ISize64.ofNat n := (rfl)
@[simp] theorem ISize64.ofBitVec_ofInt (n : Int) :
    ISize64.ofBitVec (BitVec.ofInt 64 n) = ISize64.ofInt n := (rfl)
@[simp] theorem ISize64.ofNat_bitVecToNat (n : BitVec 64) :
    ISize64.ofNat n.toNat = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp)
@[simp] theorem ISize64.ofInt_bitVecToInt (n : BitVec 64) :
    ISize64.ofInt n.toInt = ISize64.ofBitVec n :=
  ISize64.toBitVec.inj (by simp)
@[simp] theorem ISize64.ofIntTruncate_bitVecToInt (n : BitVec 64) :
    ISize64.ofIntTruncate n.toInt = ISize64.ofBitVec n :=
  toInt.inj (toInt_ofIntTruncate (by exact n.le_toInt) (by exact n.toInt_le))

@[simp] theorem ISize64.toInt_neg (n : ISize64) :
    (-n).toInt = (-n.toInt).bmod (2 ^ 64) := BitVec.toInt_neg

@[simp] theorem ISize64.toNatClampNeg_eq_zero_iff {n : ISize64} :
    n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le]
  show n.toInt ≤ 0 ↔ n.toInt ≤ (0 : ISize64).toInt
  rw [toInt_zero]

@[simp] protected theorem ISize64.not_le {n m : ISize64} : ¬n ≤ m ↔ m < n := by
  simp [le_iff_toInt_le, lt_iff_toInt_lt]

@[simp] theorem ISize64.neg_nonpos_iff (n : ISize64) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]

@[simp] theorem ISize64.toNatClampNeg_pos_iff (n : ISize64) :
    0 < n.toNatClampNeg ↔ 0 < n := by
  rw [Nat.pos_iff_ne_zero, ne_eq, toNatClampNeg_eq_zero_iff, ISize64.not_le]

@[simp] theorem ISize64.toInt_div (a b : ISize64) :
    (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, ISize64.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]

theorem ISize64.toInt_div_of_ne_left (a b : ISize64) (h : a ≠ minValue) :
    (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize64.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)

theorem ISize64.toInt_div_of_ne_right (a b : ISize64) (h : b ≠ -1) :
    (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize64.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)

@[simp] theorem ISize64.minValue_div_neg_one : minValue / -1 = minValue := (rfl)

@[simp] theorem ISize64.toInt_add (a b : ISize64) :
    (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, ISize64.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem ISize64.toInt8_add (a b : ISize64) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem ISize64.toInt16_add (a b : ISize64) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem ISize64.toInt32_add (a b : ISize64) : (a + b).toInt32 = a.toInt32 + b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem ISize64.toISize_add (a b : ISize64) : (a + b).toISize = a.toISize + b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize64.toInt_mul (a b : ISize64) :
    (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, ISize64.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem ISize64.toInt8_mul (a b : ISize64) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem ISize64.toInt16_mul (a b : ISize64) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem ISize64.toInt32_mul (a b : ISize64) : (a * b).toInt32 = a.toInt32 * b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem ISize64.toISize_mul (a b : ISize64) : (a * b).toISize = a.toISize * b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

protected theorem ISize64.sub_eq_add_neg (a b : ISize64) : a - b = a + -b :=
  ISize64.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])

@[simp] theorem ISize64.toInt_mod (a b : ISize64) :
    (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, ISize64.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]

/-!
## Lemmas from `Init.Data.SInt.Lemmas` (lines 1838–2600)

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 1838–2600.
Subtraction, ofInt arithmetic, order, algebra.
-/

@[simp] theorem ISize64.toInt_sub (a b : ISize64) :
    (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 64) := by
  simp [ISize64.sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp] theorem ISize64.toInt8_sub (a b : ISize64) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [ISize64.sub_eq_add_neg, Int8.sub_eq_add_neg]
@[simp] theorem ISize64.toInt16_sub (a b : ISize64) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [ISize64.sub_eq_add_neg, Int16.sub_eq_add_neg]
@[simp] theorem ISize64.toInt32_sub (a b : ISize64) : (a - b).toInt32 = a.toInt32 - b.toInt32 := by
  simp [ISize64.sub_eq_add_neg, Int32.sub_eq_add_neg]
@[simp] theorem ISize64.toISize_sub (a b : ISize64) : (a - b).toISize = a.toISize - b.toISize := by
  simp [ISize64.sub_eq_add_neg, ISize.sub_eq_add_neg]

@[simp] theorem ISize64.ofBitVec_neg (a : BitVec 64) : ISize64.ofBitVec (-a) = -ISize64.ofBitVec a := (rfl)

@[simp] theorem ISize64.ofInt_neg (a : Int) : ISize64.ofInt (-a) = -ISize64.ofInt a :=
  ISize64.toInt_inj.1 (by simp)

@[simp] theorem ISize64.ofBitVec_add (a b : BitVec 64) :
    ISize64.ofBitVec (a + b) = ISize64.ofBitVec a + ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofInt_add (a b : Int) :
    ISize64.ofInt (a + b) = ISize64.ofInt a + ISize64.ofInt b := by
  simp [ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize64.ofNat_add (a b : Nat) :
    ISize64.ofNat (a + b) = ISize64.ofNat a + ISize64.ofNat b := by
  simp [← ofInt_eq_ofNat, ofInt_add]

theorem ISize64.ofIntLE_add {a b : Int} {hab₁ hab₂} :
    ISize64.ofIntLE (a + b) hab₁ hab₂ = ISize64.ofInt a + ISize64.ofInt b := by
  simp [ofIntLE]

@[simp] theorem ISize64.ofBitVec_sub (a b : BitVec 64) :
    ISize64.ofBitVec (a - b) = ISize64.ofBitVec a - ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofInt_sub (a b : Int) :
    ISize64.ofInt (a - b) = ISize64.ofInt a - ISize64.ofInt b := by
  simp [Int.sub_eq_add_neg, ISize64.sub_eq_add_neg]

@[simp] theorem ISize64.ofNat_sub (a b : Nat) (hab : b ≤ a) :
    ISize64.ofNat (a - b) = ISize64.ofNat a - ISize64.ofNat b := by
  rw [← ISize64.ofInt_eq_ofNat, ← ISize64.ofInt_eq_ofNat, ← ISize64.ofInt_eq_ofNat,
    ← ISize64.ofInt_sub, Int.ofNat_sub hab]

theorem ISize64.ofIntLE_sub {a b : Int} {hab₁ hab₂} :
    ISize64.ofIntLE (a - b) hab₁ hab₂ = ISize64.ofInt a - ISize64.ofInt b := by
  simp [ofIntLE]

@[simp] theorem ISize64.ofBitVec_mul (a b : BitVec 64) :
    ISize64.ofBitVec (a * b) = ISize64.ofBitVec a * ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofInt_mul (a b : Int) :
    ISize64.ofInt (a * b) = ISize64.ofInt a * ISize64.ofInt b := by
  simp [ofInt_eq_iff_bmod_eq_toInt]

@[simp] theorem ISize64.ofNat_mul (a b : Nat) :
    ISize64.ofNat (a * b) = ISize64.ofNat a * ISize64.ofNat b := by
  simp [← ofInt_eq_ofNat, ofInt_mul]

theorem ISize64.ofIntLE_mul {a b : Int} {hab₁ hab₂} :
    ISize64.ofIntLE (a * b) hab₁ hab₂ = ISize64.ofInt a * ISize64.ofInt b := by
  simp [ofIntLE]

@[simp] theorem ISize64.ofBitVec_sdiv (a b : BitVec 64) :
    ISize64.ofBitVec (a.sdiv b) = ISize64.ofBitVec a / ISize64.ofBitVec b := (rfl)

@[simp] theorem ISize64.ofBitVec_srem (a b : BitVec 64) :
    ISize64.ofBitVec (a.srem b) = ISize64.ofBitVec a % ISize64.ofBitVec b := (rfl)

/-!
### Algebraic lemmas

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 2345–2600.
-/

protected theorem ISize64.add_assoc (a b c : ISize64) : a + b + c = a + (b + c) :=
  ISize64.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
instance : Std.Associative (α := ISize64) (· + ·) := ⟨ISize64.add_assoc⟩

protected theorem ISize64.add_comm (a b : ISize64) : a + b = b + a :=
  ISize64.toBitVec_inj.1 (BitVec.add_comm _ _)
instance : Std.Commutative (α := ISize64) (· + ·) := ⟨ISize64.add_comm⟩

@[simp] protected theorem ISize64.add_zero (a : ISize64) : a + 0 = a :=
  ISize64.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem ISize64.zero_add (a : ISize64) : 0 + a = a :=
  ISize64.toBitVec_inj.1 (BitVec.zero_add _)

@[simp] protected theorem ISize64.sub_zero (a : ISize64) : a - 0 = a :=
  ISize64.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem ISize64.zero_sub (a : ISize64) : 0 - a = -a :=
  ISize64.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem ISize64.sub_self (a : ISize64) : a - a = 0 :=
  ISize64.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem ISize64.add_left_neg (a : ISize64) : -a + a = 0 :=
  ISize64.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem ISize64.add_right_neg (a : ISize64) : a + -a = 0 :=
  ISize64.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem ISize64.sub_add_cancel (a b : ISize64) : a - b + b = a :=
  ISize64.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem ISize64.add_sub_cancel (a b : ISize64) : a + b - b = a :=
  ISize64.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

protected theorem ISize64.eq_sub_iff_add_eq {a b c : ISize64} : a = c - b ↔ a + b = c :=
  ⟨fun h => by rw [h, ISize64.sub_add_cancel], fun h => by rw [← h, ISize64.add_sub_cancel]⟩
protected theorem ISize64.sub_eq_iff_eq_add {a b c : ISize64} : a - b = c ↔ a = c + b :=
  ⟨fun h => by rw [← h, ISize64.sub_add_cancel], fun h => by rw [h, ISize64.add_sub_cancel]⟩

@[simp] protected theorem ISize64.neg_neg {a : ISize64} : - -a = a :=
  ISize64.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem ISize64.neg_inj {a b : ISize64} : -a = -b ↔ a = b := by
  simp [← ISize64.toBitVec_inj]
@[simp] protected theorem ISize64.neg_ne_zero {a : ISize64} : -a ≠ 0 ↔ a ≠ 0 := by
  simp [← ISize64.toBitVec_inj]

protected theorem ISize64.neg_add {a b : ISize64} : - (a + b) = -a - b :=
  ISize64.toBitVec_inj.1 BitVec.neg_add
@[simp] protected theorem ISize64.sub_neg {a b : ISize64} : a - -b = a + b :=
  ISize64.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem ISize64.neg_sub {a b : ISize64} : -(a - b) = b - a := by
  apply ISize64.toBitVec_inj.1
  simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_comm]

protected theorem ISize64.sub_sub (a b c : ISize64) : a - b - c = a - (b + c) := by
  simp [ISize64.sub_eq_add_neg, ISize64.add_assoc, ISize64.neg_add]

@[simp] protected theorem ISize64.add_left_inj {a b : ISize64} (c : ISize64) : (a + c = b + c) ↔ a = b := by
  constructor <;> intro h
  · have := congrArg (· - c) h; simpa using this
  · subst h; rfl
@[simp] protected theorem ISize64.add_right_inj {a b : ISize64} (c : ISize64) : (c + a = c + b) ↔ a = b := by
  rw [ISize64.add_comm c a, ISize64.add_comm c b, ISize64.add_left_inj]
@[simp] protected theorem ISize64.sub_left_inj {a b : ISize64} (c : ISize64) : (a - c = b - c) ↔ a = b := by
  simp [ISize64.sub_eq_add_neg]
@[simp] protected theorem ISize64.sub_right_inj {a b : ISize64} (c : ISize64) : (c - a = c - b) ↔ a = b := by
  simp [ISize64.sub_eq_add_neg]

@[simp] theorem ISize64.add_eq_right {a b : ISize64} : a + b = b ↔ a = 0 := by
  constructor
  · intro h; have := congrArg (· - b) h; simpa using this
  · rintro rfl; simp
@[simp] theorem ISize64.add_eq_left {a b : ISize64} : a + b = a ↔ b = 0 := by
  rw [ISize64.add_comm, ISize64.add_eq_right]
@[simp] theorem ISize64.right_eq_add {a b : ISize64} : b = a + b ↔ a = 0 := by
  rw [eq_comm, ISize64.add_eq_right]
@[simp] theorem ISize64.left_eq_add {a b : ISize64} : a = a + b ↔ b = 0 := by
  rw [eq_comm, ISize64.add_eq_left]

protected theorem ISize64.mul_comm (a b : ISize64) : a * b = b * a :=
  ISize64.toBitVec_inj.1 (BitVec.mul_comm _ _)
instance : Std.Commutative (α := ISize64) (· * ·) := ⟨ISize64.mul_comm⟩

protected theorem ISize64.mul_assoc (a b c : ISize64) : a * b * c = a * (b * c) :=
  ISize64.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
instance : Std.Associative (α := ISize64) (· * ·) := ⟨ISize64.mul_assoc⟩

@[simp] theorem ISize64.mul_one (a : ISize64) : a * 1 = a :=
  ISize64.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem ISize64.one_mul (a : ISize64) : 1 * a = a :=
  ISize64.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem ISize64.mul_zero {a : ISize64} : a * 0 = 0 :=
  ISize64.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem ISize64.zero_mul {a : ISize64} : 0 * a = 0 :=
  ISize64.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem ISize64.pow_zero (x : ISize64) : x ^ 0 = 1 := (rfl)
protected theorem ISize64.pow_succ (x : ISize64) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

protected theorem ISize64.mul_add {a b c : ISize64} : a * (b + c) = a * b + a * c :=
  ISize64.toBitVec_inj.1 BitVec.mul_add
protected theorem ISize64.add_mul {a b c : ISize64} : (a + b) * c = a * c + b * c := by
  rw [ISize64.mul_comm, ISize64.mul_add, ISize64.mul_comm a c, ISize64.mul_comm c b]

protected theorem ISize64.mul_succ {a b : ISize64} : a * (b + 1) = a * b + a := by
  simp [ISize64.mul_add]
protected theorem ISize64.succ_mul {a b : ISize64} : (a + 1) * b = a * b + b := by
  simp [ISize64.add_mul]

protected theorem ISize64.two_mul {a : ISize64} : 2 * a = a + a :=
  ISize64.toBitVec_inj.1 BitVec.two_mul
protected theorem ISize64.mul_two {a : ISize64} : a * 2 = a + a :=
  ISize64.toBitVec_inj.1 BitVec.mul_two

protected theorem ISize64.neg_mul (a b : ISize64) : -a * b = -(a * b) :=
  ISize64.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem ISize64.mul_neg (a b : ISize64) : a * -b = -(a * b) :=
  ISize64.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem ISize64.neg_mul_neg (a b : ISize64) : -a * -b = a * b :=
  ISize64.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem ISize64.neg_mul_comm (a b : ISize64) : -a * b = a * -b :=
  ISize64.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem ISize64.mul_sub {a b c : ISize64} : a * (b - c) = a * b - a * c :=
  ISize64.toBitVec_inj.1 BitVec.mul_sub
protected theorem ISize64.sub_mul {a b c : ISize64} : (a - b) * c = a * c - b * c := by
  rw [ISize64.mul_comm, ISize64.mul_sub, ISize64.mul_comm c a, ISize64.mul_comm c b]

protected theorem ISize64.add_neg_eq_sub {a b : ISize64} : a + -b = a - b :=
  ISize64.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem ISize64.neg_eq_neg_one_mul (a : ISize64) : -a = -1 * a := by
  rw [show (-1 : ISize64) = -1 from rfl, ISize64.neg_mul, ISize64.one_mul]

/-!
### Order properties

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 2783–3077.
-/

protected theorem ISize64.le_of_lt {a b : ISize64} : a < b → a ≤ b := by
  simp only [le_iff_toInt_le, lt_iff_toInt_lt]; omega

protected theorem ISize64.lt_of_le_of_ne {a b : ISize64} : a ≤ b → a ≠ b → a < b := by
  rw [le_iff_toInt_le, lt_iff_toInt_lt, ne_eq, ← toInt_inj]
  omega

protected theorem ISize64.lt_iff_le_and_ne {a b : ISize64} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simp [← ISize64.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega

@[simp] protected theorem ISize64.lt_irrefl {a : ISize64} : ¬a < a := by
  simp [lt_iff_toInt_lt]

protected theorem ISize64.lt_of_le_of_lt {a b c : ISize64} : a ≤ b → b < c → a < c := by
  simp only [le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem ISize64.lt_of_lt_of_le {a b c : ISize64} : a < b → b ≤ c → a < c := by
  simp only [le_iff_toInt_le, lt_iff_toInt_lt]; omega

@[simp] theorem ISize64.minValue_le (a : ISize64) : minValue ≤ a := by
  simpa [le_iff_toInt_le] using a.minValue_le_toInt
@[simp] theorem ISize64.le_maxValue (a : ISize64) : a ≤ maxValue := by
  simpa [le_iff_toInt_le] using a.toInt_le

@[simp] theorem ISize64.not_lt_minValue {a : ISize64} : ¬a < minValue :=
  fun h => ISize64.lt_irrefl (ISize64.lt_of_lt_of_le h (ISize64.minValue_le _))
@[simp] theorem ISize64.not_maxValue_lt {a : ISize64} : ¬maxValue < a :=
  fun h => ISize64.lt_irrefl (ISize64.lt_of_lt_of_le h (ISize64.le_maxValue _))

@[simp] protected theorem ISize64.le_refl (a : ISize64) : a ≤ a := by
  simp [ISize64.le_iff_toInt_le]
protected theorem ISize64.le_rfl {a : ISize64} : a ≤ a := ISize64.le_refl _

protected theorem ISize64.le_antisymm_iff {a b : ISize64} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h => ⟨h ▸ ISize64.le_rfl, h ▸ ISize64.le_rfl⟩,
   fun ⟨h1, h2⟩ => ISize64.toInt_inj.1 (by simp only [le_iff_toInt_le] at *; omega)⟩
protected theorem ISize64.le_antisymm {a b : ISize64} : a ≤ b → b ≤ a → a = b := by
  simpa using ISize64.le_antisymm_iff.2

@[simp] theorem ISize64.le_minValue_iff {a : ISize64} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => ISize64.le_antisymm h (ISize64.minValue_le _), fun h => h ▸ ISize64.le_rfl⟩
@[simp] theorem ISize64.maxValue_le_iff {a : ISize64} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => (ISize64.le_antisymm h (ISize64.le_maxValue _)).symm, fun h => h ▸ ISize64.le_rfl⟩

@[simp] protected theorem ISize64.zero_div {a : ISize64} : 0 / a = 0 :=
  ISize64.toBitVec_inj.1 BitVec.zero_sdiv
@[simp] protected theorem ISize64.div_zero {a : ISize64} : a / 0 = 0 :=
  ISize64.toBitVec_inj.1 BitVec.sdiv_zero
@[simp] protected theorem ISize64.div_one {a : ISize64} : a / 1 = a :=
  ISize64.toBitVec_inj.1 BitVec.sdiv_one
protected theorem ISize64.div_self {a : ISize64} : a / a = if a = 0 then 0 else 1 := by
  simp [← ISize64.toBitVec_inj, apply_ite]

@[simp] protected theorem ISize64.mod_zero {a : ISize64} : a % 0 = a :=
  ISize64.toBitVec_inj.1 BitVec.srem_zero
@[simp] protected theorem ISize64.zero_mod {a : ISize64} : 0 % a = 0 :=
  ISize64.toBitVec_inj.1 BitVec.zero_srem
@[simp] protected theorem ISize64.mod_one {a : ISize64} : a % 1 = 0 :=
  ISize64.toBitVec_inj.1 BitVec.srem_one
@[simp] protected theorem ISize64.mod_self {a : ISize64} : a % a = 0 :=
  ISize64.toBitVec_inj.1 BitVec.srem_self

protected theorem ISize64.le_trans {a b c : ISize64} : a ≤ b → b ≤ c → a ≤ c := by
  simp only [le_iff_toInt_le]; omega
protected theorem ISize64.lt_trans {a b c : ISize64} : a < b → b < c → a < c := by
  simp only [lt_iff_toInt_lt]; omega
protected theorem ISize64.le_total (a b : ISize64) : a ≤ b ∨ b ≤ a := by
  simp only [le_iff_toInt_le]; omega
protected theorem ISize64.lt_asymm {a b : ISize64} : a < b → ¬b < a :=
  fun hab hba => ISize64.lt_irrefl (ISize64.lt_trans hab hba)

protected theorem ISize64.lt_or_lt_of_ne {a b : ISize64} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← ISize64.toInt_inj]; omega
protected theorem ISize64.lt_or_le (a b : ISize64) : a < b ∨ b ≤ a := by
  simp only [lt_iff_toInt_lt, le_iff_toInt_le]; omega
protected theorem ISize64.le_or_lt (a b : ISize64) : a ≤ b ∨ b < a :=
  (b.lt_or_le a).symm
protected theorem ISize64.le_of_eq {a b : ISize64} : a = b → a ≤ b := (· ▸ ISize64.le_rfl)
protected theorem ISize64.le_iff_lt_or_eq {a b : ISize64} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← ISize64.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem ISize64.lt_or_eq_of_le {a b : ISize64} : a ≤ b → a < b ∨ a = b :=
  ISize64.le_iff_lt_or_eq.mp

protected theorem ISize64.ne_of_lt {a b : ISize64} : a < b → a ≠ b := by
  simpa [ISize64.lt_iff_toInt_lt, ← ISize64.toInt_inj] using Int.ne_of_lt

theorem ISize64.toInt_eq_toNatClampNeg {a : ISize64} (ha : 0 ≤ a) :
    a.toInt = a.toNatClampNeg := by
  rw [cast_toNatClampNeg _ ha]

/-!
## UInt64-related cross-conversion lemmas

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), various lines up to 1840.
-/

@[simp] theorem ISize64.ofBitVec_uInt64ToBitVec (x : UInt64) :
    ISize64.ofBitVec x.toBitVec = x.toISize64 := (rfl)

theorem ISize64.ofIntLE_int8ToInt (x : Int8) {h₁ h₂} :
    ISize64.ofIntLE x.toInt h₁ h₂ = x.toISize64 := (rfl)
theorem ISize64.ofIntLE_int16ToInt (x : Int16) {h₁ h₂} :
    ISize64.ofIntLE x.toInt h₁ h₂ = x.toISize64 := (rfl)
theorem ISize64.ofIntLE_int32ToInt (x : Int32) {h₁ h₂} :
    ISize64.ofIntLE x.toInt h₁ h₂ = x.toISize64 := (rfl)
@[simp] theorem ISize64.ofIntLE_iSizeToInt (x : ISize) :
    ISize64.ofIntLE x.toInt (Int.le_trans (by decide) x.le_toInt)
      (Int.le_of_lt_add_one x.toInt_lt) = x.toISize64 := (rfl)

@[simp, int_toBitVec] theorem ISize64.toBitVec_toUInt64 (x : ISize64) :
    x.toUInt64.toBitVec = x.toBitVec := (rfl)

theorem ISize64.toFin_toBitVec (x : ISize64) :
    x.toBitVec.toFin = x.toUInt64.toFin := (rfl)

@[simp] theorem ISize64.toInt64_toUInt64 (x : ISize64) :
    x.toUInt64.toInt64 = x.toInt64 := (rfl)

theorem ISize64.toNat_toBitVec (x : ISize64) :
    x.toBitVec.toNat = x.toUInt64.toNat := (rfl)

theorem ISize64.toNat_toBitVec_of_le {x : ISize64} (hx : 0 ≤ x) :
    x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm

theorem ISize64.toNat_toUInt64_of_le {x : ISize64} (hx : 0 ≤ x) :
    x.toUInt64.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]

@[simp] theorem ISize64.toUInt64_ofNat' {n} :
    (ISize64.ofNat n).toUInt64 = UInt64.ofNat n := (rfl)
@[simp] theorem ISize64.toUInt64_ofNat {n} :
    toUInt64 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)

/-!
## Additional items from lines 1840–2600

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 1840–2600.
-/

instance : Std.LawfulIdentity (α := ISize64) (· + ·) 0 where
  left_id := ISize64.zero_add
  right_id := ISize64.add_zero

theorem ISize64.toNatClampNeg_one : (1 : ISize64).toNatClampNeg = 1 := (rfl)

theorem ISize64.toInt_one : (1 : ISize64).toInt = 1 := (rfl)

theorem ISize64.zero_lt_one : (0 : ISize64) < 1 := by
  rw [lt_iff_toInt_lt, toInt_zero, toInt_one]; decide

theorem ISize64.zero_ne_one : (0 : ISize64) ≠ 1 := by
  rw [ne_eq, ← toInt_inj, toInt_zero, toInt_one]; decide

theorem ISize64.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide

theorem ISize64.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 63 := (rfl)

theorem ISize64.ofBitVec_le_iff_sle (a b : BitVec 64) :
    ISize64.ofBitVec a ≤ ISize64.ofBitVec b ↔ a.sle b := Iff.rfl

theorem ISize64.ofBitVec_lt_iff_slt (a b : BitVec 64) :
    ISize64.ofBitVec a < ISize64.ofBitVec b ↔ a.slt b := Iff.rfl

theorem ISize64.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofIntLE a ha₁ ha₂ ≤ ISize64.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by
  simp [le_iff_toInt_le]

theorem ISize64.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofIntLE a ha₁ ha₂ < ISize64.ofIntLE b hb₁ hb₂ ↔ a < b := by
  simp [lt_iff_toInt_lt]

theorem ISize64.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) :
    ISize64.ofInt a ≤ ISize64.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]

theorem ISize64.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) :
    ISize64.ofInt a < ISize64.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]

theorem ISize64.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat a ≤ ISize64.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat,
    ofInt_le_iff_le (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega)
      (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega),
    Int.ofNat_le]

theorem ISize64.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat a < ISize64.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat,
    ofInt_lt_iff_lt (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega)
      (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega),
    Int.ofNat_lt]

theorem ISize64.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) :
    ISize64.ofInt (a.tdiv b) = ISize64.ofInt a / ISize64.ofInt b := by
  rw [ISize64.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem ISize64.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofInt (a.tdiv b) = ISize64.ofIntLE a ha₁ ha₂ / ISize64.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]

theorem ISize64.ofNat_div {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat (a / b) = ISize64.ofNat a / ISize64.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega)
      (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega)]

/-!
## Remaining items from lines 2600–3492

Adapted from Init/Data/SInt/Lemmas.lean (Lean v4.29.0-rc1), lines 2600–3492 (end of file).
-/

instance : Std.LawfulCommIdentity (α := ISize64) (· * ·) 1 where
  right_id := ISize64.mul_one

theorem ISize64.neg_add_mul_eq_mul_not {a b : ISize64} : -(a + a * b) = a * ~~~b :=
  ISize64.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem ISize64.neg_mul_not_eq_add_mul {a b : ISize64} : -(a * ~~~b) = a + a * b :=
  ISize64.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

@[simp] protected theorem ISize64.not_lt {a b : ISize64} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]

@[simp] theorem ISize64.toUInt64_add (a b : ISize64) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := (rfl)
@[simp] theorem ISize64.toUInt64_neg (a : ISize64) : (-a).toUInt64 = -a.toUInt64 := (rfl)
@[simp] theorem ISize64.toUInt64_sub (a b : ISize64) : (a - b).toUInt64 = a.toUInt64 - b.toUInt64 := (rfl)
@[simp] theorem ISize64.toUInt64_mul (a b : ISize64) : (a * b).toUInt64 = a.toUInt64 * b.toUInt64 := (rfl)

theorem ISize64.toNatClampNeg_le {a b : ISize64} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← ISize64.toNat_toInt, ← ISize64.toNat_toInt]
  exact Int.toNat_le_toNat (ISize64.le_iff_toInt_le.1 hab)

theorem ISize64.toUInt64_le {a b : ISize64} (ha : 0 ≤ a) (hab : a ≤ b) :
    a.toUInt64 ≤ b.toUInt64 := by
  rw [UInt64.le_iff_toNat_le, toNat_toUInt64_of_le ha, toNat_toUInt64_of_le (ISize64.le_trans ha hab)]
  exact ISize64.toNatClampNeg_le hab

theorem ISize64.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 63) : 0 ≤ ISize64.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, ISize64.toInt_zero]
  exact Int.natCast_nonneg _

protected theorem ISize64.sub_nonneg_of_le {a b : ISize64} (hb : 0 ≤ b) (hab : b ≤ a) :
    0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (ISize64.le_trans hb hab),
    ← ofNat_sub _ _ (ISize64.toNatClampNeg_le hab)]
  exact ISize64.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)

theorem ISize64.toNatClampNeg_sub_of_le {a b : ISize64} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt64_of_le (ISize64.sub_nonneg_of_le hb hab), toUInt64_sub,
    UInt64.toNat_sub_of_le _ _ (ISize64.toUInt64_le hb hab),
    ← toNat_toUInt64_of_le (ISize64.le_trans hb hab), ← toNat_toUInt64_of_le hb]

theorem ISize64.toInt_sub_of_le (a b : ISize64) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [ISize64.toInt_eq_toNatClampNeg (ISize64.sub_nonneg_of_le hb h),
    ISize64.toInt_eq_toNatClampNeg (ISize64.le_trans hb h), ISize64.toInt_eq_toNatClampNeg hb,
    ISize64.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact ISize64.toNatClampNeg_le h

protected theorem ISize64.sub_le {a b : ISize64} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  rw [le_iff_toInt_le, ISize64.toInt_sub_of_le _ _ hb hab]
  have := le_iff_toInt_le.1 hb
  rw [toInt_zero] at this
  omega

protected theorem ISize64.sub_lt {a b : ISize64} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  rw [lt_iff_toInt_lt, ISize64.toInt_sub_of_le _ _ (ISize64.le_of_lt hb) hab]
  have := lt_iff_toInt_lt.1 hb
  rw [toInt_zero] at this
  omega

theorem ISize64.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) :
    ISize64.ofInt (a.tmod b) = ISize64.ofInt a % ISize64.ofInt b := by
  rw [ISize64.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂

theorem ISize64.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize64.ofInt (a.tmod b) = ISize64.ofIntLE a ha₁ ha₂ % ISize64.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]

open Std in
instance ISize64.instIsLinearOrder : IsLinearOrder ISize64 := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply ISize64.le_antisymm
  case le_total => constructor; apply ISize64.le_total
  case le_trans => constructor; apply ISize64.le_trans

open Std in
instance : LawfulOrderLT ISize64 where
  lt_iff := by
    simp [← ISize64.not_le, Decidable.imp_iff_not_or, Total.total]

theorem ISize64.ofNat_mod {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ISize64.ofNat (a % b) = ISize64.ofNat a % ISize64.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega)
      (by rw [toInt_minValue]; omega) (by rw [toInt_maxValue]; omega)]

/-!
## Grind's ToInt

For grind to use integer arithmetic on `ISize64`, we need the following instances.

Adapted from Init/GrindInstances/ToInt.lean (Lean v4.29.0-rc1), lines 445–481.
-/

namespace Lean.Grind

instance : ToInt ISize64 (.sint 64) where
  toInt x := x.toInt
  toInt_inj x y w := private ISize64.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨ISize64.le_toInt x, ISize64.toInt_lt x⟩

@[simp] theorem toInt_isize64 (x : ISize64) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero ISize64 (.sint 64) where
  toInt_zero := by
    change (0 : ISize64).toInt = _
    rw [ISize64.toInt_zero]

instance : ToInt.OfNat ISize64 (.sint 64) where
  toInt_ofNat x := by
    rw [toInt_isize64, ISize64.toInt_ofNat, ISize64.size, Int64.size,
      Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add ISize64 (.sint 64) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul ISize64 (.sint 64) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE ISize64 (.sint 64) where
  le_iff x y := by simpa using ISize64.le_iff_toInt_le

instance : ToInt.LT ISize64 (.sint 64) where
  lt_iff x y := by simpa using ISize64.lt_iff_toInt_lt

/-!
### Ring structure

Adapted from Init/GrindInstances/Ring/SInt.lean (Lean v4.29.0-rc1), lines 189–241.
-/

@[expose, instance_reducible]
def ISize64.natCast : NatCast ISize64 where
  natCast x := ISize64.ofNat x

@[expose, instance_reducible]
def ISize64.intCast : IntCast ISize64 where
  intCast x := ISize64.ofInt x

attribute [local instance] ISize64.intCast in
theorem ISize64.intCast_neg (i : Int) : ((-i : Int) : ISize64) = -(i : ISize64) :=
  ISize64.ofInt_neg _

attribute [local instance] ISize64.intCast in
theorem ISize64.intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : ISize64) = OfNat.ofNat x :=
  ISize64.ofInt_eq_ofNat

attribute [local instance] ISize64.natCast ISize64.intCast in
instance : CommRing ISize64 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := ISize64.add_assoc
  add_comm := ISize64.add_comm
  add_zero := ISize64.add_zero
  neg_add_cancel := ISize64.add_left_neg
  mul_assoc := ISize64.mul_assoc
  mul_comm := ISize64.mul_comm
  mul_one := ISize64.mul_one
  one_mul := ISize64.one_mul
  left_distrib _ _ _ := ISize64.mul_add
  right_distrib _ _ _ := ISize64.add_mul
  zero_mul _ := ISize64.zero_mul
  mul_zero _ := ISize64.mul_zero
  sub_eq_add_neg := ISize64.sub_eq_add_neg
  pow_zero := ISize64.pow_zero
  pow_succ := ISize64.pow_succ
  ofNat_succ x := ISize64.ofNat_add x 1
  intCast_neg := ISize64.ofInt_neg
  neg_zsmul i x := by
    change (-i : Int) * x = - (i * x)
    simp [ISize64.intCast_neg, ISize64.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (ISize64.intCast_ofNat _)

instance : IsCharP ISize64 (2 ^ 64) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = ISize64.ofInt x := rfl
    rw [this]
    simp only [ISize64.ofInt_eq_iff_bmod_eq_toInt, ISize64.toInt_zero]
    constructor
    · intro h; rw [← Nat.dvd_iff_mod_eq_zero]; exact Int.ofNat_dvd_right.mp (Int.dvd_of_bmod_eq_zero h)
    · intro h; exact Int.bmod_eq_zero_of_dvd (Int.ofNat_dvd_right.mpr (Nat.dvd_iff_mod_eq_zero.mpr h)))

instance : ToInt.Pow ISize64 (.sint 64) := ToInt.pow_of_semiring (by simp)

end Lean.Grind


/-!
## Simp-Procs

Adapted from Lean/Meta/Tactic/Simp/BuiltinSimprocs/SInt.lean (Lean v4.29.0-rc1), lines 16–111.
The builtin macro uses `builtin_dsimproc`/`builtin_simproc`; we use `dsimproc`/`simproc`
since ISize64 is not a built-in type.
-/

namespace ISize64
open Lean Meta Simp

instance : ToExpr ISize64 where
  toTypeExpr := mkConst ``ISize64
  toExpr a :=
    if a.toInt ≥ 0 then
      let r := mkRawNatLit a.toNatClampNeg
      mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``ISize64) r
        (.app (.const ``ISize64.instOfNat []) r)
    else
      let r := mkRawNatLit (-a).toNatClampNeg
      mkApp2 (.const ``Neg.neg [0])
        (mkConst ``ISize64)
        (mkApp3 (.const ``OfNat.ofNat [0]) (mkConst ``ISize64) r
          (.app (.const ``ISize64.instOfNat []) r))

def fromExpr (e : Expr) : SimpM (Option ISize64) := do
  if let some (n, _) ← getOfNatValue? e `ISize64 then
    return some (ISize64.ofNat n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a `ISize64 | return none
  return some (ISize64.ofInt (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : ISize64 → ISize64 → ISize64) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : ISize64 → ISize64 → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : ISize64 → ISize64 → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← (fromExpr e.appFn!.appArg!) | return .continue
  let some m ← (fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

dsimproc [simp, seval] reduceNeg ((- _ : ISize64)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← (fromExpr arg) | return .continue
    return .done <| toExpr (- v)

dsimproc [simp, seval] reduceAdd ((_ + _ : ISize64)) := reduceBin ``HAdd.hAdd 6 (· + ·)
dsimproc [simp, seval] reduceMul ((_ * _ : ISize64)) := reduceBin ``HMul.hMul 6 (· * ·)
dsimproc [simp, seval] reduceSub ((_ - _ : ISize64)) := reduceBin ``HSub.hSub 6 (· - ·)
dsimproc [simp, seval] reduceDiv ((_ / _ : ISize64)) := reduceBin ``HDiv.hDiv 6 (· / ·)
dsimproc [simp, seval] reduceMod ((_ % _ : ISize64)) := reduceBin ``HMod.hMod 6 (· % ·)

simproc [simp, seval] reduceLT  (( _ : ISize64) < _)  := reduceBinPred ``LT.lt 4 (. < .)
simproc [simp, seval] reduceLE  (( _ : ISize64) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT  (( _ : ISize64) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE  (( _ : ISize64) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
simproc [simp, seval] reduceEq  (( _ : ISize64) = _)  := reduceBinPred ``Eq 3 (. = .)
simproc [simp, seval] reduceNe  (( _ : ISize64) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
dsimproc [simp, seval] reduceBEq  (( _ : ISize64) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
dsimproc [simp, seval] reduceBNe  (( _ : ISize64) != _)  := reduceBoolPred ``bne 4 (. != .)

dsimproc [simp, seval] reduceOfIntLE (ISize64.ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity `ISize64.ofIntLE 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := ISize64.ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfNat (ISize64.ofNat _) := fun e => do
  unless e.isAppOfArity `ISize64.ofNat 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := ISize64.ofNat value
  return .done <| toExpr value

dsimproc [simp, seval] reduceOfInt (ISize64.ofInt _) := fun e => do
  unless e.isAppOfArity `ISize64.ofInt 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := ISize64.ofInt value
  return .done <| toExpr value

dsimproc [simp, seval] reduceToInt (ISize64.toInt _) := fun e => do
  unless e.isAppOfArity `ISize64.toInt 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := ISize64.toInt v
  return .done <| toExpr n

dsimproc [simp, seval] reduceToNatClampNeg (ISize64.toNatClampNeg _) := fun e => do
  unless e.isAppOfArity `ISize64.toNatClampNeg 1 do return .continue
  let some v ← (fromExpr e.appArg!) | return .continue
  let n := ISize64.toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for ISize64 values. We don't want to unfold in the symbolic evaluator. -/
dsimproc [seval] isValue ((OfNat.ofNat _ : ISize64)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end ISize64
