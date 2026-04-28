import Aeneas

open Aeneas.Std

namespace core

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

inductive cmp.Ordering where
| Less : cmp.Ordering
| Equal : cmp.Ordering
| Greater : cmp.Ordering

structure clone.Clone (Self : Type) where
  clone : Self → Result Self

structure marker.Copy (Self : Type) where
  cloneInst : clone.Clone Self

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

end core

namespace hax_lib

def int.Int := _root_.Int

end hax_lib
