import CoreModels.Alloc.Funs

namespace alloc

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
def slice.Slice.to_vec
  {T : Type} (cloneInst : core_models.clone.Clone T) (s : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (vec.Vec T alloc.Global) :=
  slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def slice.Slice.into_vec
  {T : Type} (A : Type) (s : Aeneas.Std.Slice T) : Aeneas.Std.Result (vec.Vec T A) :=
  slice.Dummy.into_vec A s

end

def vec.Vec.new := @vec.VecTGlobal.new
def vec.Vec.with_capacity := @vec.VecTGlobal.with_capacity

end alloc
