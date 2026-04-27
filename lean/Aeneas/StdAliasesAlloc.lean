/-
  Std-name-map aliases for items extracted from the local `alloc` crate.
  Loads after `Aeneas.Alloc.Funs`. Kept separate from `Aeneas.StdAliases`
  so that `Alloc.Funs` itself can depend on `StdAliases` (no cycle).
-/
import Aeneas.Primitives
import Aeneas.Types
import Aeneas.Alloc.Funs

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
