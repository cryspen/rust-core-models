import Aeneas

open Aeneas.Std

namespace CoreModels.core

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

/-! ## Option

Rust's `Option` aliased to Lean's built-in

-/

namespace option

abbrev Option := _root_.Option
@[match_pattern] abbrev Option.Some {T} (x : T) : Option T := _root_.Option.some x
@[match_pattern] abbrev Option.None {T} : Option T := _root_.Option.none

end option

inductive cmp.Ordering where
| Less : cmp.Ordering
| Equal : cmp.Ordering
| Greater : cmp.Ordering

end CoreModels.core

namespace CoreModels

/-! ## Rust's `Result` enum — declared in a guard namespace to avoid a
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

namespace _AeneasResultGuard
inductive core.result.Result (T : Type) (E : Type) where
| Ok : T → core.result.Result T E
| Err : E → core.result.Result T E
end _AeneasResultGuard

namespace core.result
@[reducible] def Result (T E : Type) : Type :=
  _root_.CoreModels._AeneasResultGuard.core.result.Result T E
@[match_pattern]
abbrev Result.Ok {T E : Type} (t : T) : Result T E :=
  _root_.CoreModels._AeneasResultGuard.core.result.Result.Ok t
@[match_pattern]
abbrev Result.Err {T E : Type} (e : E) : Result T E :=
  _root_.CoreModels._AeneasResultGuard.core.result.Result.Err e

/-- `Result<T, E>::ok(self) -> Option<T>`. Defined as an `abbrev` (not
    `def`) so it doesn't auto-create the `core.result.Result` namespace
    (which would re-introduce the monadic-`Result` shadowing this whole
    setup is designed to avoid). -/
abbrev Result.ok {T E : Type} (r : Result T E) : Aeneas.Std.Result (_root_.Option T) :=
  match r with
  | Result.Ok t  => Aeneas.Std.Result.ok (some t)
  | Result.Err _ => Aeneas.Std.Result.ok none

/-- `Result<T, E>::err(self) -> Option<E>`. Same `abbrev` rationale. -/
abbrev Result.err {T E : Type} (r : Result T E) : Aeneas.Std.Result (_root_.Option E) :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok none
  | Result.Err e => Aeneas.Std.Result.ok (some e)

/-- `Result<T, E>::is_ok(&self) -> bool`. -/
abbrev Result.is_ok {T E : Type} (r : Result T E) : Aeneas.Std.Result Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok true
  | Result.Err _ => Aeneas.Std.Result.ok false

/-- `Result<T, E>::is_err(&self) -> bool`. -/
abbrev Result.is_err {T E : Type} (r : Result T E) : Aeneas.Std.Result Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok false
  | Result.Err _ => Aeneas.Std.Result.ok true
end core.result


/-! ## Hax lib -/
namespace hax_lib

def int.Int := _root_.Int

end hax_lib

export Aeneas.Std (
  core.clone.Clone core.marker.Copy
)

end CoreModels
