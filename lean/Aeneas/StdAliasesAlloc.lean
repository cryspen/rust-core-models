/-
  Std-name-map aliases for items extracted from the local `alloc` crate.
  Loads after `Aeneas.Alloc.Funs`. Kept separate from `Aeneas.StdAliases`
  so that `Alloc.Funs` itself can depend on `StdAliases` (no cycle).
-/
import Aeneas.Primitives
import Aeneas.Types
import Aeneas.Alloc.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

/-! ## `[T]::to_vec` and `Box<[T]>::into_vec`

Aeneas's builtin name map turns `<[T]>::to_vec` into a reference to
`alloc.slice.Slice.to_vec` (and similarly for `into_vec`). Our local
`alloc/` crate provides those bodies, but under the `alloc.slice.Dummy`
namespace because of the standard "you can't `impl` for a foreign slice
type" workaround. Re-export them at the std-map name so downstream
extractions land on a defined symbol.
-/

noncomputable section

@[rust_fun "alloc::slice::{[@T]}::to_vec"]
def alloc.slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T) :
  Result (alloc.vec.Vec T) :=
  alloc.slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def alloc.slice.Slice.into_vec
  {T : Type} (A : Type) (s : Slice T) : Result (alloc.vec.Vec T) :=
  alloc.slice.Dummy.into_vec A s

end

/-! ## `alloc::vec::Vec::index` (currently disabled)

The generic `<Vec<T,A> as Index<I>>::index` impl is excluded from the
alloc extraction at the LLBC level (see `ALLOC_CHARON_EXCLUDES` in the
parent `Makefile`) — it depends on `core::slice::index::SliceIndex`,
which is itself excluded for shape-mismatch reasons (see
`StdAliases.lean`). The placeholder alias below is kept commented as a
TODO for the eventual full modeling pass.

```
noncomputable section
@[rust_fun "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, @O>}::index"]
abbrev alloc.vec.Vec.index :=
  @_root_.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
end
```
-/
