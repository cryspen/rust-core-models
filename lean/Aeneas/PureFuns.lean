/-
  Pure (non-monadic) versions of functions that Aeneas marks as `can_fail:false`.

  When Aeneas extracts a call to one of these functions, it does NOT wrap it
  in the `Result` monad. So our model must provide them as pure functions for
  extracted code to typecheck against the model.

  Source: https://github.com/AeneasVerif/aeneas/blob/main/src/extract/ExtractBuiltinLean.ml
  (entries marked with `~can_fail:false`)
-/
import Aeneas.Primitives
import Aeneas.Types

namespace core

/-! ## core::option::Option -/

namespace option.Option

def unwrap_or {T : Type} (self : option.Option T) (default : T) : T :=
  match self with
  | option.Option.None    => default
  | option.Option.Some x  => x

def is_some {T : Type} (self : option.Option T) : Bool :=
  match self with
  | option.Option.Some _ => true
  | option.Option.None   => false

def is_none {T : Type} (self : option.Option T) : Bool :=
  match self with
  | option.Option.None   => true
  | option.Option.Some _ => false

/-- Replaces `self` with `None` and returns the original. -/
def take {T : Type} (self : option.Option T) : option.Option T × option.Option T :=
  (self, option.Option.None)

end option.Option

/-! ## core::mem -/

namespace mem

/-- Acts like a swap in the functional pure world: returns the old `dst` paired
    with the new `dst` (which is `src`). -/
def replace {T : Type} (dst : T) (src : T) : T × T := (dst, src)

def swap {T : Type} (a : T) (b : T) : T × T := (b, a)

end mem

/-! ## core::convert::From<T, T> -/

namespace convert

def FromSame.from_ {T : Type} (x : T) : T := x

end convert

/-! ## core::slice -/

def slice.Slice.len {T : Type} (s : _root_.core.Slice T) : Std.Usize :=
  _root_.core.Slice.len s

def slice.Slice.reverse {T : Type} (s : _root_.core.Slice T) : _root_.core.Slice T :=
  ⟨s.val.reverse, by simpa using s.property⟩

/-! ## core::num — wrapping / saturating / rotate / overflowing arithmetic

Aeneas (`src/extract/ExtractBuiltin.ml`, function `mk_scalar_funs`) marks these
ops as pure (`~can_fail:false`) for every integer type, with extraction names
of the form `core.num.<U8|U16|...>.<wrapping_add|wrapping_sub|...>`. We provide
pure shims here using bit-vector arithmetic. -/

namespace num

attribute [-instance]
  instHAddUInt8Result
  instHAddUInt16Result
  instHAddUInt32Result
  instHAddUInt64Result
  instHAddUInt128Result
  instHAddUSize64Result
  instHSubUInt8Result
  instHSubUInt16Result
  instHSubUInt32Result
  instHSubUInt64Result
  instHSubUInt128Result
  instHSubUSize64Result
  instHMulUInt8Result
  instHMulUInt16Result
  instHMulUInt32Result
  instHMulUInt64Result
  instHMulUInt128Result
  instHMulUSize64Result
  instHAddInt8Result
  instHAddInt16Result
  instHAddInt32Result
  instHAddInt64Result
  instHAddInt128Result
  instHAddISize64Result
  instHSubInt8Result
  instHSubInt16Result
  instHSubInt32Result
  instHSubInt64Result
  instHSubInt128Result
  instHSubISize64Result
  instHMulInt8Result
  instHMulInt16Result
  instHMulInt32Result
  instHMulInt64Result
  instHMulInt128Result
  instHMulISize64Result

-- Unsigned wrapping
def U8.wrapping_add    (x y : U8)    : U8    := x + y
def U16.wrapping_add   (x y : U16)   : U16   := x + y
def U32.wrapping_add   (x y : U32)   : U32   := x + y
def U64.wrapping_add   (x y : U64)   : U64   := x + y
def U128.wrapping_add  (x y : U128)  : U128  := x + y
def Usize.wrapping_add (x y : Usize) : Usize := x + y

def U8.wrapping_sub    (x y : U8)    : U8    := x - y
def U16.wrapping_sub   (x y : U16)   : U16   := x - y
def U32.wrapping_sub   (x y : U32)   : U32   := x - y
def U64.wrapping_sub   (x y : U64)   : U64   := x - y
def U128.wrapping_sub  (x y : U128)  : U128  := x - y
def Usize.wrapping_sub (x y : Usize) : Usize := x - y

def U8.wrapping_mul    (x y : U8)    : U8    := x * y
def U16.wrapping_mul   (x y : U16)   : U16   := x * y
def U32.wrapping_mul   (x y : U32)   : U32   := x * y
def U64.wrapping_mul   (x y : U64)   : U64   := x * y
def U128.wrapping_mul  (x y : U128)  : U128  := x * y
def Usize.wrapping_mul (x y : Usize) : Usize := x * y

-- Signed wrapping
def I8.wrapping_add    (x y : I8)    : I8    := x + y
def I16.wrapping_add   (x y : I16)   : I16   := x + y
def I32.wrapping_add   (x y : I32)   : I32   := x + y
def I64.wrapping_add   (x y : I64)   : I64   := x + y
def I128.wrapping_add  (x y : I128)  : I128  := x + y
def Isize.wrapping_add (x y : Isize) : Isize := x + y

def I8.wrapping_sub    (x y : I8)    : I8    := x - y
def I16.wrapping_sub   (x y : I16)   : I16   := x - y
def I32.wrapping_sub   (x y : I32)   : I32   := x - y
def I64.wrapping_sub   (x y : I64)   : I64   := x - y
def I128.wrapping_sub  (x y : I128)  : I128  := x - y
def Isize.wrapping_sub (x y : Isize) : Isize := x - y

def I8.wrapping_mul    (x y : I8)    : I8    := x * y
def I16.wrapping_mul   (x y : I16)   : I16   := x * y
def I32.wrapping_mul   (x y : I32)   : I32   := x * y
def I64.wrapping_mul   (x y : I64)   : I64   := x * y
def I128.wrapping_mul  (x y : I128)  : I128  := x * y
def Isize.wrapping_mul (x y : Isize) : Isize := x * y

def U8.saturating_add    (x y : U8)    : U8    := .ofNat (min core.num.U8.MAX.toNat (x.toNat + y.toNat))
def U16.saturating_add   (x y : U16)   : U16   := .ofNat (min core.num.U16.MAX.toNat (x.toNat + y.toNat))
def U32.saturating_add   (x y : U32)   : U32   := .ofNat (min core.num.U32.MAX.toNat (x.toNat + y.toNat))
def U64.saturating_add   (x y : U64)   : U64   := .ofNat (min core.num.U64.MAX.toNat (x.toNat + y.toNat))
def U128.saturating_add  (x y : U128)  : U128  := .ofNat (min core.num.U128.MAX.toNat (x.toNat + y.toNat))
def Usize.saturating_add (x y : Usize) : Usize := .ofNat (min core.num.Usize.MAX.toNat (x.toNat + y.toNat))

def U8.saturating_sub    (x y : U8)    : U8    := .ofNat (x.toNat - y.toNat)
def U16.saturating_sub   (x y : U16)   : U16   := .ofNat (x.toNat - y.toNat)
def U32.saturating_sub   (x y : U32)   : U32   := .ofNat (x.toNat - y.toNat)
def U64.saturating_sub   (x y : U64)   : U64   := .ofNat (x.toNat - y.toNat)
def U128.saturating_sub  (x y : U128)  : U128  := .ofNat (x.toNat - y.toNat)
def Usize.saturating_sub (x y : Usize) : Usize := .ofNat (x.toNat - y.toNat)

def I8.saturating_add    (x y : I8)    : I8    := .ofInt (max core.num.I8.MIN.toInt (min core.num.I8.MAX.toInt (x.toInt + y.toInt)))
def I16.saturating_add   (x y : I16)   : I16   := .ofInt (max core.num.I16.MIN.toInt (min core.num.I16.MAX.toInt (x.toInt + y.toInt)))
def I32.saturating_add   (x y : I32)   : I32   := .ofInt (max core.num.I32.MIN.toInt (min core.num.I32.MAX.toInt (x.toInt + y.toInt)))
def I64.saturating_add   (x y : I64)   : I64   := .ofInt (max core.num.I64.MIN.toInt (min core.num.I64.MAX.toInt (x.toInt + y.toInt)))
def I128.saturating_add  (x y : I128)  : I128  := .ofInt (max core.num.I128.MIN.toInt (min core.num.I128.MAX.toInt (x.toInt + y.toInt)))
def Isize.saturating_add (x y : Isize) : Isize := .ofInt (max core.num.Isize.MIN.toInt (min core.num.Isize.MAX.toInt (x.toInt + y.toInt)))

def I8.saturating_sub    (x y : I8)    : I8    := .ofInt (max core.num.I8.MIN.toInt (min core.num.I8.MAX.toInt (x.toInt - y.toInt)))
def I16.saturating_sub   (x y : I16)   : I16   := .ofInt (max core.num.I16.MIN.toInt (min core.num.I16.MAX.toInt (x.toInt - y.toInt)))
def I32.saturating_sub   (x y : I32)   : I32   := .ofInt (max core.num.I32.MIN.toInt (min core.num.I32.MAX.toInt (x.toInt - y.toInt)))
def I64.saturating_sub   (x y : I64)   : I64   := .ofInt (max core.num.I64.MIN.toInt (min core.num.I64.MAX.toInt (x.toInt - y.toInt)))
def I128.saturating_sub  (x y : I128)  : I128  := .ofInt (max core.num.I128.MIN.toInt (min core.num.I128.MAX.toInt (x.toInt - y.toInt)))
def Isize.saturating_sub (x y : Isize) : Isize := .ofInt (max core.num.Isize.MIN.toInt (min core.num.Isize.MAX.toInt (x.toInt - y.toInt)))

-- overflowing_add returns (sum, overflowed)
def U8.overflowing_add    (x y : U8)    : U8    × Bool := (x + y, x.toNat + y.toNat > core.num.U8.MAX.toNat)
def U16.overflowing_add   (x y : U16)   : U16   × Bool := (x + y, x.toNat + y.toNat > core.num.U16.MAX.toNat)
def U32.overflowing_add   (x y : U32)   : U32   × Bool := (x + y, x.toNat + y.toNat > core.num.U32.MAX.toNat)
def U64.overflowing_add   (x y : U64)   : U64   × Bool := (x + y, x.toNat + y.toNat > core.num.U64.MAX.toNat)
def U128.overflowing_add  (x y : U128)  : U128  × Bool := (x + y, x.toNat + y.toNat > core.num.U128.MAX.toNat)
def Usize.overflowing_add (x y : Usize) : Usize × Bool := (x + y, x.toNat + y.toNat > core.num.Usize.MAX.toNat)
def I8.overflowing_add    (x y : I8)    : I8    × Bool := (x + y, x.toInt + y.toInt < core.num.I8.MIN.toInt ∨ x.toInt + y.toInt > core.num.I8.MAX.toInt)
def I16.overflowing_add   (x y : I16)   : I16   × Bool := (x + y, x.toInt + y.toInt < core.num.I16.MIN.toInt ∨ x.toInt + y.toInt > core.num.I16.MAX.toInt)
def I32.overflowing_add   (x y : I32)   : I32   × Bool := (x + y, x.toInt + y.toInt < core.num.I32.MIN.toInt ∨ x.toInt + y.toInt > core.num.I32.MAX.toInt)
def I64.overflowing_add   (x y : I64)   : I64   × Bool := (x + y, x.toInt + y.toInt < core.num.I64.MIN.toInt ∨ x.toInt + y.toInt > core.num.I64.MAX.toInt)
def I128.overflowing_add  (x y : I128)  : I128  × Bool := (x + y, x.toInt + y.toInt < core.num.I128.MIN.toInt ∨ x.toInt + y.toInt > core.num.I128.MAX.toInt)
def Isize.overflowing_add (x y : Isize) : Isize × Bool := (x + y, x.toInt + y.toInt < core.num.Isize.MIN.toInt ∨ x.toInt + y.toInt > core.num.Isize.MAX.toInt)

-- rotate_left / rotate_right take a u32 amount in Rust
def U8.rotate_left    (x : U8)    (n : U32) : U8    := ⟨x.toBitVec.rotateLeft n.toNat⟩
def U16.rotate_left   (x : U16)   (n : U32) : U16   := ⟨x.toBitVec.rotateLeft n.toNat⟩
def U32.rotate_left   (x : U32)   (n : U32) : U32   := ⟨x.toBitVec.rotateLeft n.toNat⟩
def U64.rotate_left   (x : U64)   (n : U32) : U64   := ⟨x.toBitVec.rotateLeft n.toNat⟩
def U128.rotate_left  (x : U128)  (n : U32) : U128  := ⟨x.toBitVec.rotateLeft n.toNat⟩
def Usize.rotate_left (x : Usize) (n : U32) : Usize := ⟨x.toBitVec.rotateLeft n.toNat⟩
def I8.rotate_left    (x : I8)    (n : U32) : I8    := ⟨⟨x.toBitVec.rotateLeft n.toNat⟩⟩
def I16.rotate_left   (x : I16)   (n : U32) : I16   := ⟨⟨x.toBitVec.rotateLeft n.toNat⟩⟩
def I32.rotate_left   (x : I32)   (n : U32) : I32   := ⟨⟨x.toBitVec.rotateLeft n.toNat⟩⟩
def I64.rotate_left   (x : I64)   (n : U32) : I64   := ⟨⟨x.toBitVec.rotateLeft n.toNat⟩⟩
def I128.rotate_left  (x : I128)  (n : U32) : I128  := ⟨⟨x.toBitVec.rotateLeft n.toNat⟩⟩
def Isize.rotate_left (x : Isize) (n : U32) : Isize := ⟨⟨x.toBitVec.rotateLeft n.toNat⟩⟩

def U8.rotate_right    (x : U8)    (n : U32) : U8    := ⟨x.toBitVec.rotateRight n.toNat⟩
def U16.rotate_right   (x : U16)   (n : U32) : U16   := ⟨x.toBitVec.rotateRight n.toNat⟩
def U32.rotate_right   (x : U32)   (n : U32) : U32   := ⟨x.toBitVec.rotateRight n.toNat⟩
def U64.rotate_right   (x : U64)   (n : U32) : U64   := ⟨x.toBitVec.rotateRight n.toNat⟩
def U128.rotate_right  (x : U128)  (n : U32) : U128  := ⟨x.toBitVec.rotateRight n.toNat⟩
def Usize.rotate_right (x : Usize) (n : U32) : Usize := ⟨x.toBitVec.rotateRight n.toNat⟩
def I8.rotate_right    (x : I8)    (n : U32) : I8    := ⟨⟨x.toBitVec.rotateRight n.toNat⟩⟩
def I16.rotate_right   (x : I16)   (n : U32) : I16   := ⟨⟨x.toBitVec.rotateRight n.toNat⟩⟩
def I32.rotate_right   (x : I32)   (n : U32) : I32   := ⟨⟨x.toBitVec.rotateRight n.toNat⟩⟩
def I64.rotate_right   (x : I64)   (n : U32) : I64   := ⟨⟨x.toBitVec.rotateRight n.toNat⟩⟩
def I128.rotate_right  (x : I128)  (n : U32) : I128  := ⟨⟨x.toBitVec.rotateRight n.toNat⟩⟩
def Isize.rotate_right (x : Isize) (n : U32) : Isize := ⟨⟨x.toBitVec.rotateRight n.toNat⟩⟩

end num

end core
