import CoreModels.Alloc.Funs

namespace CoreModels

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
  {T : Type} (cloneInst : core.clone.Clone T) (s : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (alloc.vec.Vec T) :=
  alloc.slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def alloc.slice.Slice.into_vec
  {T : Type} (A : Type) (s : Aeneas.Std.Slice T) : Aeneas.Std.Result (alloc.vec.Vec T) :=
  alloc.slice.Dummy.into_vec A s

end

end CoreModels
