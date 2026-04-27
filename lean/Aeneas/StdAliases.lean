/-
  Std-name-map aliases that load **after** `Aeneas.Funs` but **before**
  `Aeneas.Alloc.Funs`. Anything `Aeneas.Alloc.Funs` itself needs to
  reference (because Aeneas emits a downstream-style call into the
  alloc body) goes here.

  Alias-only items that depend on `Alloc.Funs` go in `StdAliasesAlloc`.

  This file exists only because `Aeneas.FunsExternal` imports
  `Aeneas.PureFuns`, which prevents `PureFuns` from depending on `Funs`.
-/
import Aeneas.Primitives
import Aeneas.Types
import Aeneas.Funs

/-! ## `core::slice::index` (currently disabled)

The `core::slice::index::SliceIndex` trait and its impls are excluded
from extraction at the LLBC level (see `CHARON_EXCLUDES` in the parent
`Makefile`) — Aeneas's name map for std's `SliceIndex` constructs a
7-field record (`sealedInst`, `get`, `get_mut`, `get_unchecked`,
`get_unchecked_mut`, `index`, `index_mut`) plus a `Sealed` super-trait
that we do not yet model in the Rust source. Rather than ship a
half-baked 2-field shim that breaks downstream record construction, we
exclude the trait entirely. Downstream Aeneas extractions that try to
reach `core.slice.index.Slice.index`, `core.slice.index.SliceIndexUsizeSlice`
etc. will fail to elaborate — that is the intended signal.

The aliases below are kept commented as a TODO for the eventual full
modeling pass (see the `aeneas-test` regression crate for the call
sites that need them).

```
@[rust_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"]
def core.slice.index.Slice.index :=
  @_root_.core.Slice.Insts.Core_modelsOpsIndexIndex.index

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<[@T], @T> for usize}"]
abbrev core.slice.index.SliceIndexUsizeSlice :=
  @_root_.core.Usize.Insts.Core_modelsSliceIndexSliceIndexSliceT
…
```
-/
