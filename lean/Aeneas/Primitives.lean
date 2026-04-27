/-
  Primitives for the CoreModels library.
  Minimal definitions to compile Aeneas-generated code without depending on Aeneas.
-/
import Lean
import Aeneas.MissingLean
import Aeneas.ISize64

/-!
# No-op Aeneas attributes
-/

section RustAttributes

open Lean in
syntax (name := rust_type) "rust_type" str : attr
open Lean in
initialize registerBuiltinAttribute {
  name := `rust_type
  descr := "Rust type name pattern (no-op)"
  add := fun _ _ _ => pure ()
}

open Lean in
syntax (name := rust_fun) "rust_fun" str : attr
open Lean in
initialize registerBuiltinAttribute {
  name := `rust_fun
  descr := "Rust function name pattern (no-op)"
  add := fun _ _ _ => pure ()
}

open Lean in
syntax (name := rust_trait_impl) "rust_trait_impl" str : attr
open Lean in
initialize registerBuiltinAttribute {
  name := `rust_trait_impl
  descr := "Rust trait impl name pattern (no-op)"
  add := fun _ _ _ => pure ()
}

open Lean in
syntax (name := rust_trait) "rust_trait" str
  (("(" ident ":=" "[" str,* "]" ")")*) : attr
open Lean in
initialize registerBuiltinAttribute {
  name := `rust_trait
  descr := "Rust trait name pattern (no-op)"
  add := fun _ _ _ => pure ()
}

open Lean in
syntax (name := rust_const) "rust_const" str : attr
open Lean in
initialize registerBuiltinAttribute {
  name := `rust_const
  descr := "Rust const name pattern (no-op)"
  add := fun _ _ _ => pure ()
}

open Lean in
syntax (name := discriminant) "discriminant" ident (("[" term,* "]")?) : attr
open Lean in
initialize registerBuiltinAttribute {
  name := `discriminant
  descr := "Discriminant values (no-op)"
  add := fun _ _ _ => pure ()
}

register_simp_attr rust_loop
register_simp_attr rust_loop_body
register_simp_attr global_simps

/-!
## No-op linter options

Aeneas extraction emits `set_option linter.dupNamespace false` and
`set_option linter.hashCommand false`. These linters live in Mathlib/Batteries,
which we don't depend on. Register them as boolean options so the `set_option`
commands don't error out.
-/

register_option linter.dupNamespace : Bool := {
  defValue := false
  descr := "(no-op stub) duplicate namespace linter"
}

register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "(no-op stub) hashCommand linter"
}

end RustAttributes

/-!
# Core namespace — all Aeneas-compatible primitives
-/

namespace core

/-! ## Phantom — used by `Aeneas/Alloc/Types.lean` rewrite

`vec.Vec T A` in core-models is `Seq T × PhantomData<A>`. We can't reuse
the existing `core.marker.PhantomData T := T` for the alloc rewrite (the
extracted constructor sites use `()`, which is `Unit`). We instead rewrite
the `core.marker.PhantomData A` field type to `core.Phantom A`.

`Phantom` is a *non-reducible* `structure` with a phantom type parameter:
the parameter must appear syntactically in the type for generic-allocator
type inference to keep working at call sites (`alloc.vec.Vec.clear` etc.
take the `A` implicit). A `@[reducible] def Phantom _ := Unit` would
defeat that. -/

structure Phantom (A : Type) where mk ::
deriving Inhabited

/-! ## Error and Result -/

inductive Error where
   | assertionFailure | integerOverflow | divisionByZero
   | arrayOutOfBounds | maximumSizeExceeded | panic | undef
deriving Repr, BEq, DecidableEq

def Result (α : Type) := ExceptT Error Option α

namespace Result

-- These `Except` instances are missing in Lean's library.
-- We use them to derive the corresponding `RustM` instances below.
deriving instance BEq, DecidableEq for Except

instance instBEq {α : Type} [BEq α] : BEq (Result α) :=
  inferInstanceAs (BEq (Option (Except Error α)))
instance instDecidableEq {α : Type} [DecidableEq α] : DecidableEq (Result α) :=
  inferInstanceAs (DecidableEq (Option (Except Error α)))
instance instInhabited {α : Type} : Inhabited (Result α) :=
  inferInstanceAs (Inhabited (Option (Except Error α)))
instance instMonad : Monad Result :=
  inferInstanceAs (Monad (ExceptT Error Option))
instance instLawfulMonad : LawfulMonad Result :=
  inferInstanceAs (LawfulMonad (ExceptT Error Option))

@[reducible, match_pattern] def ok {α : Type} (v : α) : Result α := some (.ok v)
@[reducible, match_pattern] def fail {α : Type} (e : Error) : Result α := some (.error e)
@[reducible, match_pattern] def div {α : Type} : Result α := none

instance {α : Type} [Repr α] : Repr (Result α) where
  reprPrec x prec := match x with
    | .ok v   => Repr.addAppParen (f!"Result.ok {reprArg v}") prec
    | .fail e => Repr.addAppParen (f!"Result.fail {reprArg e}") prec
    | .div    => "Result.div"

/- Monad instances for `mvcgen`: -/

section Std.Do
open Std.Do

instance instWP : WP Result (.except Error (.except PUnit .pure)) :=
  inferInstanceAs (WP (ExceptT Error Option) _)
instance instWPMonad : WPMonad Result (.except Error (.except PUnit .pure)) :=
  inferInstanceAs (WPMonad (ExceptT Error Option) _)

end Std.Do

end Result

open Result Error

def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then ok () else fail assertionFailure

def lift {α : Type} (x : α) : Result α := ok x

@[simp] abbrev liftFun1 {α β} (f : α → β) : α → Result β := fun x => ok (f x)
@[simp] abbrev liftFun2 {α β γ : Type} (f : α → β → γ) : α → β → Result γ := fun x y => ok (f x y)

/-! ## ControlFlow -/

inductive ControlFlow (α : Type) (β : Type) where
  | cont (v : α) | done (v : β)
deriving Repr, BEq

/-! ## Loop -/

def loop {α : Type} {β : Type} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  match body x with
  | ok r =>
    match r with
    | ControlFlow.cont x => loop body x
    | ControlFlow.done x => ok x
  | fail e => fail e
  | div => div
partial_fixpoint

/-! ## Machine Integers -/

inductive UScalarTy where | Usize | U8 | U16 | U32 | U64 | U128
inductive IScalarTy where | Isize | I8 | I16 | I32 | I64 | I128

abbrev U8    := UInt8
abbrev U16   := UInt16
abbrev U32   := UInt32
abbrev U64   := UInt64
abbrev U128  := UInt128
abbrev Usize := USize64

abbrev I8    := Int8
abbrev I16   := Int16
abbrev I32   := Int32
abbrev I64   := Int64
abbrev I128  := Int128
abbrev Isize := ISize64

class UScalar (α : Type) where
  toNat : α → Nat
  ofNat : Nat → α

class HasUScalarTy (ty : UScalarTy) (α : outParam Type) [UScalar α] where

instance : UScalar U8    where toNat := UInt8.toNat;   ofNat := UInt8.ofNat
instance : UScalar U16   where toNat := UInt16.toNat;  ofNat := UInt16.ofNat
instance : UScalar U32   where toNat := UInt32.toNat;  ofNat := UInt32.ofNat
instance : UScalar U64   where toNat := UInt64.toNat;  ofNat := UInt64.ofNat
instance : UScalar U128  where toNat := UInt128.toNat; ofNat := UInt128.ofNat
instance : UScalar Usize where toNat := USize64.toNat; ofNat := USize64.ofNat

instance : HasUScalarTy UScalarTy.U8    U8    where
instance : HasUScalarTy UScalarTy.U16   U16   where
instance : HasUScalarTy UScalarTy.U32   U32   where
instance : HasUScalarTy UScalarTy.U64   U64   where
instance : HasUScalarTy UScalarTy.U128  U128  where
instance : HasUScalarTy UScalarTy.Usize Usize where

def UScalar.cast (target : UScalarTy) [UScalar α] [HasUScalarTy target α] [UScalar β]
    (x : β) : α :=
  UScalar.ofNat (UScalar.toNat x)

class IScalar (α : Type) where
  toInt : α → Int
  ofInt : Int → α

class HasIScalarTy (ty : IScalarTy) (α : outParam Type) [IScalar α] where

instance : IScalar I8    where toInt := Int8.toInt;    ofInt := Int8.ofInt
instance : IScalar I16   where toInt := Int16.toInt;   ofInt := Int16.ofInt
instance : IScalar I32   where toInt := Int32.toInt;   ofInt := Int32.ofInt
instance : IScalar I64   where toInt := Int64.toInt;   ofInt := Int64.ofInt
instance : IScalar I128  where toInt := Int128.toInt;  ofInt := Int128.ofInt
instance : IScalar Isize where toInt := ISize64.toInt; ofInt := ISize64.ofInt

instance : HasIScalarTy IScalarTy.I8    I8    where
instance : HasIScalarTy IScalarTy.I16   I16   where
instance : HasIScalarTy IScalarTy.I32   I32   where
instance : HasIScalarTy IScalarTy.I64   I64   where
instance : HasIScalarTy IScalarTy.I128  I128  where
instance : HasIScalarTy IScalarTy.Isize Isize where

def IScalar.cast (target : IScalarTy) [IScalar α] [HasIScalarTy target α] [IScalar β]
    (x : β) : α :=
  IScalar.ofInt (IScalar.toInt x)


/-! ### Scalar arithmetic -/

open Lean in
set_option hygiene false in
macro "declare_scalar_arith" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do
  let signed ← match s.raw[0].getKind with
  | `signed   => pure true
  | `unsigned => pure false
  | _         => throw .unsupportedSyntax
  let ofInt := mkIdent (typeName.getId ++ `ofInt)
  if signed then
    return ← `(
      instance : HAdd $typeName $typeName (Result $typeName) where
        hAdd a b :=
          let s := a.toInt + b.toInt
          if -(2 ^ ($width - 1)) ≤ s ∧ s < 2 ^ ($width - 1) then ok ($ofInt s) else fail Error.integerOverflow
      instance : HSub $typeName $typeName (Result $typeName) where
        hSub a b :=
          let s := a.toInt - b.toInt
          if -(2 ^ ($width - 1)) ≤ s ∧ s < 2 ^ ($width - 1) then ok ($ofInt s) else fail Error.integerOverflow
      instance : HMul $typeName $typeName (Result $typeName) where
        hMul a b :=
          let p := a.toInt * b.toInt
          if -(2 ^ ($width - 1)) ≤ p ∧ p < 2 ^ ($width - 1) then ok ($ofInt p) else fail Error.integerOverflow
      instance : HDiv $typeName $typeName (Result $typeName) where
        hDiv a b :=
          if b.toInt = 0 then fail Error.divisionByZero
          else if a.toInt = -(2 ^ ($width - 1)) ∧ b.toInt = -1 then fail Error.integerOverflow
          else ok ($ofInt (a.toInt / b.toInt))
      instance : HMod $typeName $typeName (Result $typeName) where
        hMod a b :=
          if b.toInt = 0 then fail Error.divisionByZero
          else if a.toInt = -(2 ^ ($width - 1)) ∧ b.toInt = -1 then fail Error.integerOverflow
          else ok ($ofInt (a.toInt % b.toInt))
      instance : HAnd $typeName $typeName $typeName where
        hAnd a b := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
      instance : HOr $typeName $typeName $typeName where
        hOr a b := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
      instance : HXor $typeName $typeName $typeName where
        hXor a b := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
    )
  else
    return ← `(
      instance : HAdd $typeName $typeName (Result $typeName) where
        hAdd a b :=
          let s := a.toNat + b.toNat
          if s < 2 ^ $width then ok ($(mkIdent (typeName.getId ++ `ofNat)) s) else fail Error.integerOverflow
      instance : HSub $typeName $typeName (Result $typeName) where
        hSub a b :=
          if b.toNat ≤ a.toNat then ok ($(mkIdent (typeName.getId ++ `ofNat)) (a.toNat - b.toNat)) else fail Error.integerOverflow
      instance : HMul $typeName $typeName (Result $typeName) where
        hMul a b :=
          let p := a.toNat * b.toNat
          if p < 2 ^ $width then ok ($(mkIdent (typeName.getId ++ `ofNat)) p) else fail Error.integerOverflow
      instance : HDiv $typeName $typeName (Result $typeName) where
        hDiv a b := if b.toNat = 0 then fail Error.divisionByZero else ok ($(mkIdent (typeName.getId ++ `ofNat)) (a.toNat / b.toNat))
      instance : HMod $typeName $typeName (Result $typeName) where
        hMod a b := if b.toNat = 0 then fail Error.divisionByZero else ok ($(mkIdent (typeName.getId ++ `ofNat)) (a.toNat % b.toNat))
      instance : HAnd $typeName $typeName $typeName where
        hAnd a b := ⟨a.toBitVec &&& b.toBitVec⟩
      instance : HOr $typeName $typeName $typeName where
        hOr a b := ⟨a.toBitVec ||| b.toBitVec⟩
      instance : HXor $typeName $typeName $typeName where
        hXor a b := ⟨a.toBitVec ^^^ b.toBitVec⟩
    )

declare_scalar_arith unsigned UInt8 8
declare_scalar_arith unsigned UInt16 16
declare_scalar_arith unsigned UInt32 32
declare_scalar_arith unsigned UInt64 64
declare_scalar_arith unsigned UInt128 128
declare_scalar_arith unsigned USize64 64

declare_scalar_arith signed Int8 8
declare_scalar_arith signed Int16 16
declare_scalar_arith signed Int32 32
declare_scalar_arith signed Int64 64
declare_scalar_arith signed Int128 128
declare_scalar_arith signed ISize64 64

/-! ### Scalar literal notations -/

macro:max x:term:max noWs "#u8"    : term => `(UInt8.ofNat $x)
macro:max x:term:max noWs "#u16"   : term => `(UInt16.ofNat $x)
macro:max x:term:max noWs "#u32"   : term => `(UInt32.ofNat $x)
macro:max x:term:max noWs "#u64"   : term => `(UInt64.ofNat $x)
macro:max x:term:max noWs "#u128"  : term => `(UInt128.ofNat $x)
macro:max x:term:max noWs "#usize" : term => `(USize64.ofNat $x)

macro:max x:term:max noWs "#i8"    : term => `(Int8.ofInt $x)
macro:max x:term:max noWs "#i16"   : term => `(Int16.ofInt $x)
macro:max x:term:max noWs "#i32"   : term => `(Int32.ofInt $x)
macro:max x:term:max noWs "#i64"   : term => `(Int64.ofInt $x)
macro:max x:term:max noWs "#i128"  : term => `(Int128.ofInt $x)
macro:max x:term:max noWs "#isize" : term => `(ISize64.ofInt $x)

/-! ### Numeric bounds

These need to be defined here (forward declared) because the generated
`Funs.lean` references them BEFORE the file's own bounds definitions appear.
The patcher comments out the duplicate generated defs. -/

namespace num
def U8.MAX    : U8    := 255#u8
def U8.MIN    : U8    := 0#u8
def U16.MAX   : U16   := 65535#u16
def U16.MIN   : U16   := 0#u16
def U32.MAX   : U32   := 4294967295#u32
def U32.MIN   : U32   := 0#u32
def U64.MAX   : U64   := 18446744073709551615#u64
def U64.MIN   : U64   := 0#u64
def U128.MAX  : U128  := 340282366920938463463374607431768211455#u128
def U128.MIN  : U128  := 0#u128
def Usize.MAX : Usize := 18446744073709551615#usize
def Usize.MIN : Usize := 0#usize
def I8.MAX    : I8    := 127#i8
def I8.MIN    : I8    := (-128)#i8
def I16.MAX   : I16   := 32767#i16
def I16.MIN   : I16   := (-32768)#i16
def I32.MAX   : I32   := 2147483647#i32
def I32.MIN   : I32   := (-2147483648)#i32
def I64.MAX   : I64   := 9223372036854775807#i64
def I64.MIN   : I64   := (-9223372036854775808)#i64
def I128.MAX  : I128  := 170141183460469231731687303715884105727#i128
def I128.MIN  : I128  := (-170141183460469231731687303715884105728)#i128
def Isize.MAX : Isize := 9223372036854775807#isize
def Isize.MIN : Isize := (-9223372036854775808)#isize
end num


/-! ## Slice and Array -/

def Slice (α : Type) := { l : List α // l.length ≤ 18446744073709551615 }

instance (α : Type) : CoeOut (Slice α) (List α) where coe v := v.val
instance [BEq α] : BEq (Slice α) where beq a b := a.val == b.val

def Slice.length {α : Type} (v : Slice α) : Nat := v.val.length
def Slice.len {α : Type} (v : Slice α) : Usize := USize64.ofNat v.val.length
def Slice.new (α : Type) : Slice α := ⟨[], by simp⟩

def Array (α : Type) (n : Usize) := { l : List α // l.length = n.toNat }

instance (α : Type) (n : Usize) : CoeOut (Array α n) (List α) where coe v := v.val
instance [BEq α] {n : Usize} : BEq (Array α n) where beq a b := a.val == b.val

def Array.length {α : Type} {n : Usize} (v : Array α n) : Nat := v.val.length
def Array.empty (α : Type) : Array α (.ofNat 0) :=
  ⟨[], by simp⟩

/-! ### Aeneas-compatible Array helpers

These match `Aeneas.Std.Array.*` so that downstream Aeneas-extracted code
that calls e.g. `Array.index_usize`, `Array.make`, etc. resolves correctly.
-/

def Array.make {α : Type} (n : Usize) (init : List α)
    (hl : init.length = n.toNat := by
      first | rfl | (simp; first | rfl | native_decide) | native_decide) :
    Array α n :=
  ⟨init, hl⟩

def Array.repeat {α : Type} (n : Usize) (x : α) : Array α n :=
  ⟨List.replicate n.toNat x, by simp⟩

def Array.to_slice {α : Type} {n : Usize} (v : Array α n) : Slice α :=
  ⟨v.val, by
    have hlen : v.val.length = n.toNat := v.property
    have hbv  : n.toBitVec.toNat < 2 ^ 64 := n.toBitVec.isLt
    show v.val.length ≤ 18446744073709551615
    rw [hlen]
    show n.toBitVec.toNat ≤ _
    omega⟩

def Array.index_usize {α : Type} {n : Usize} (v : Array α n) (i : Usize) :
    Result α :=
  match v.val[i.toNat]? with
  | none   => fail Error.arrayOutOfBounds
  | some x => ok x

def Slice.index_usize {α : Type} (v : Slice α) (i : Usize) : Result α :=
  match v.val[i.toNat]? with
  | none   => fail Error.arrayOutOfBounds
  | some x => ok x

def Slice.index_mut_usize {α : Type} (v : Slice α) (i : Usize) :
    Result (α × (α → Slice α)) :=
  match v.val[i.toNat]? with
  | none   => fail Error.arrayOutOfBounds
  | some x => ok (x, fun y => ⟨v.val.set i.toNat y, by have := v.property; simp [*]⟩)

def Array.update {α : Type} {n : Usize} (v : Array α n) (i : Usize) (x : α) :
    Result (Array α n) :=
  match v.val[i.toNat]? with
  | none   => fail Error.arrayOutOfBounds
  | some _ => ok ⟨v.val.set i.toNat x, by have := v.property; simp [*]⟩

-- `core.array.CloneArray.clone` and `core.array.equality.PartialEqArray.eq`
-- are provided by `Aeneas.Instances` (they need `core.cmp.PartialEq` and
-- `core.clone.Clone` which are forward-declared further down this file).

/-! ## `dyn Trait` trait objects

Aeneas extracts Rust's `dyn Trait` types as `Dyn (fun _dyn => Trait _dyn)`.
The Lean model pairs an underlying type with a value of that type and the
corresponding trait instance, erasing it behind an existential wrapper.

The trait-constraint argument has type `Type → Type` (the body returns the
elaborated trait structure, which lives in `Type`). -/

structure Dyn (F : Type → Type) where
  Self : Type
  value : Self
  inst : F Self

/-! ## Raw pointers

Aeneas models Rust's `*const T` and `*mut T` opaquely — there is no Lean
machinery for pointer arithmetic or dereferencing, but the *types* must
exist so signatures referencing them elaborate. We represent each as a
1-argument alias of the pointee type; this is enough for the extraction
to typecheck. -/

def ConstRawPtr (T : Type) : Type := T
def MutRawPtr   (T : Type) : Type := T

/-! ## Forward declarations for things Types.lean references before defining them -/

/-! ### Rust's `Option` aliased to Lean's built-in -/

namespace option
abbrev Option := _root_.Option
@[match_pattern] abbrev Option.Some {T} (x : T) : Option T := _root_.Option.some x
@[match_pattern] abbrev Option.None {T} : Option T := _root_.Option.none
end option

/-! ### Rust's `Result` enum — declared in a guard namespace to avoid a
    name-shadowing trap.

A Rust `Result<T, E>` extracts to the *type* path `core.result.Result T E`.
Naïvely declaring `inductive core.result.Result T E` at that path causes
trouble: any later `def core.result.Result.<m>` (and similarly `axiom
core.result.Result.<m>` in `FunsExternal_Template.lean`) is placed in the
namespace `core.result.Result`. When Lean elaborates the body, bare
`Result` is resolved by walking up enclosing namespaces — and the very
first hit is `core.result.Result` itself (the inductive). The monadic
`Result` (= `core.Result`) is shadowed and the signature fails to
elaborate, e.g.

    axiom core.result.Result.ok :
      core.result.Result T E → Result (Option T)
    -- error: type expected, got (Result (Option T) : Type → Type)

The trick used by Aeneas's stdlib is to declare the inductive *inside*
its `Aeneas.Std` namespace (so the full path becomes
`Aeneas.Std.core.result.Result`). When downstream code defines
`def core.result.Result.foo`, the namespace `core.result.Result` it opens
is fresh — no `Result` member, lookup falls through, monad wins.

We do the same here: declare the inductive inside `_AeneasResultGuard`
and re-expose it as a *reducible* `core.result.Result` alias plus
`@[match_pattern]` constructor abbrevs. Aliases (`abbrev` / `@[reducible]
def`) do **not** create an auto-namespace, so the path
`core.result.Result.*` remains free for downstream extraction to populate
without shadow.

NOTE: the cleanest fix would be **upstream**: rename Aeneas's monadic
`Result` to something that can never collide with the Rust enum, e.g.
`RustM`. That would let us drop this guard namespace, the
`TYPES_TO_REMOVE` entry for `core_models::result::Result`, and the
companion `qualify_result_in_result_defs` patcher pass entirely. -/

end core

namespace _AeneasResultGuard
inductive core.result.Result (T : Type) (E : Type) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E
end _AeneasResultGuard

namespace core.result
@[reducible] def Result (T E : Type) : Type :=
  _root_._AeneasResultGuard.core.result.Result T E
@[match_pattern]
abbrev Result.Ok {T E : Type} (t : T) : Result T E :=
  _root_._AeneasResultGuard.core.result.Result.Ok t
@[match_pattern]
abbrev Result.Err {T E : Type} (e : E) : Result T E :=
  _root_._AeneasResultGuard.core.result.Result.Err e

/-- `Result<T, E>::ok(self) -> Option<T>`. Defined as an `abbrev` (not
    `def`) so it doesn't auto-create the `core.result.Result` namespace
    (which would re-introduce the monadic-`Result` shadowing this whole
    setup is designed to avoid). -/
abbrev Result.ok {T E : Type} (r : Result T E) : _root_.core.Result (_root_.Option T) :=
  match r with
  | Result.Ok t  => _root_.core.Result.ok (some t)
  | Result.Err _ => _root_.core.Result.ok none

/-- `Result<T, E>::err(self) -> Option<E>`. Same `abbrev` rationale. -/
abbrev Result.err {T E : Type} (r : Result T E) : _root_.core.Result (_root_.Option E) :=
  match r with
  | Result.Ok _  => _root_.core.Result.ok none
  | Result.Err e => _root_.core.Result.ok (some e)

/-- `Result<T, E>::is_ok(&self) -> bool`. -/
abbrev Result.is_ok {T E : Type} (r : Result T E) : _root_.core.Result Bool :=
  match r with
  | Result.Ok _  => _root_.core.Result.ok true
  | Result.Err _ => _root_.core.Result.ok false

/-- `Result<T, E>::is_err(&self) -> bool`. -/
abbrev Result.is_err {T E : Type} (r : Result T E) : _root_.core.Result Bool :=
  match r with
  | Result.Ok _  => _root_.core.Result.ok false
  | Result.Err _ => _root_.core.Result.ok true
end core.result

namespace core

structure clone.Clone (Self : Type) where
  clone : Self → Result Self

structure marker.Copy (Self : Type) where
  cloneInst : clone.Clone Self

/-! ### Scalar Clone / Copy instances

Aeneas's standard library names them `core.clone.CloneU8`, `core.marker.CopyU8`,
etc. Downstream Aeneas-extracted code that calls e.g. `<u64 as Clone>::clone`
references these exact names. -/

private def builtinScalarClone {α : Type} : clone.Clone α where
  clone := fun x => Result.ok x

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

namespace ops.function
structure FnOnce (Self : Type) (Args : Type) (Self_Output : Type) where
  call_once : Self → Args → Result Self_Output

structure FnMut (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnOnceInst : FnOnce Self Args Self_Clause0_Output
  call_mut : Self → Args → Result (Self_Clause0_Output × Self)

structure Fn (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnMutInst : FnMut Self Args Self_Clause0_Output
  call : Self → Args → Result Self_Clause0_Output
end ops.function

/-! ## PartialEq eq accessors (referenced as core.cmp.impls.PartialEqU8.eq etc.) -/

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

/-! ## Std sub-namespace (for Std.Usize, Std.Array, etc. references) -/

namespace Std
  export _root_.core (
    Error Result ControlFlow
    UScalar IScalar UScalarTy IScalarTy
    U8 U16 U32 U64 U128 Usize
    I8 I16 I32 I64 I128 Isize
    Slice Array
    massert lift liftFun1 liftFun2
  )
  -- Re-export Array.empty so Std.Array.empty works
  def Array.empty := @_root_.core.Array.empty
end Std

end core

/-!
# Aeneas namespace aliases

So that downstream code doing `open Aeneas Aeneas.Std Result ControlFlow Error` works.
-/

namespace Aeneas
  namespace Std
    export _root_.core (
      Error Result ControlFlow
      UScalar IScalar UScalarTy IScalarTy
      U8 U16 U32 U64 U128 Usize
      I8 I16 I32 I64 I128 Isize
      Slice Array
      massert lift liftFun1 liftFun2
      loop
    )
    def Array.empty       := @_root_.core.Array.empty
    def Array.make        := @_root_.core.Array.make
    def Array.repeat      := @_root_.core.Array.repeat
    def Array.to_slice    := @_root_.core.Array.to_slice
    def Array.index_usize := @_root_.core.Array.index_usize
    def Array.update      := @_root_.core.Array.update
    def Slice.len             := @_root_.core.Slice.len
    def Slice.index_usize     := @_root_.core.Slice.index_usize
    def Slice.index_mut_usize := @_root_.core.Slice.index_mut_usize
    namespace Result
      export _root_.core.Result (ok fail div)
    end Result
    namespace ControlFlow
      export _root_.core.ControlFlow (cont done)
    end ControlFlow
    namespace Error
      export _root_.core.Error (assertionFailure integerOverflow divisionByZero arrayOutOfBounds maximumSizeExceeded panic undef)
    end Error
  end Std
  export Std (
    Error Result ControlFlow
    UScalar IScalar UScalarTy IScalarTy
    U8 U16 U32 U64 U128 Usize
    I8 I16 I32 I64 I128 Isize
    Slice Array
    massert lift liftFun1 liftFun2
    loop
  )
end Aeneas
