# aeneas-compat

Estimate a crate's compatibility with the `CoreModels` Aeneas library.

There are two tools here, working at different altitudes:

- **`aeneas_compat.py`** (described below) — a *pre-flight estimate* from the
  crate's charon **LLBC**, before you run aeneas. Needs only `charon`. Fast, but
  the covered set is derived from the model's LLBC rather than its Lean library,
  so it has known false-positive categories (see bottom).
- **`lean_extract_compat.py`** — a *post-extraction* check from the crate's
  aeneas-emitted **Lean**. The most precise of the tools, but needs the crate to
  have been extracted by aeneas already. See
  [The Lean-extraction check](#the-lean-extraction-check).

Given a target crate, it reports:

- **used** — the `core::*` / `alloc::*` / `std::*` items the crate actually
  reaches (after charon has desugared operators, resolved trait dispatch, etc.);
- **covered** — those the model in this repo provides;
- **MISSING** — those it does not, i.e. the gaps you'd hit.

## Usage

```sh
# on a crate (runs charon for you):
python3 tools/aeneas-compat/aeneas_compat.py path/to/crate

# on an already-built LLBC (skips charon on the target):
python3 tools/aeneas-compat/aeneas_compat.py --llbc path/to/target.llbc

# machine-readable (for the planned axiom / exclude-flag generators):
python3 tools/aeneas-compat/aeneas_compat.py --llbc target.llbc --json
```

It needs `charon` on `PATH` (override with `--charon` or `$CHARON`) and the
model LLBCs `core_models.llbc` / `alloc.llbc` at the repo root (build them with
`make llbc alloc-llbc` — they are git-ignored artifacts).

Useful flags: `--show-covered`, `--no-manifest` (raw auto-derived result),
`--manifest PATH`, `--rustflags` (defaults to `--cfg charon`, matching the main
Makefile).

## How it works

Everything is read out of charon's **LLBC**, which is the right altitude for
this question: the external (`core`/`alloc`/`std`) items in a crate's LLBC are
*exactly* what aeneas will need the library to resolve. A source-level (`syn`)
scan would miss operator desugaring (`a == b` → `PartialEq::eq`), trait-method
resolution and deref coercions — charon has already done all of that.

- **used set** — `charon pretty-print` the target LLBC and collect every
  fully-qualified path under `core` / `alloc` / `std`.
- **covered set** — same, over the model's own LLBCs. Anything `core`/`alloc`/
  `std` that the model *defines* (its `core_models::*` / `alloc_models::*`
  items, renamed back) **or** *references and still extracts against* is treated
  as provided.
- **MISSING** = used − covered − manifest.

Items are matched on a **module-independent key**: generics and lifetimes are
stripped, and trait impls are keyed on `{impl Trait for Type}::method` rather
than the module they are authored in (the model often writes an impl in a
different module than real core — e.g. `impl Default for u8` lives in
`core_models::num`, not `core::default`).

## The manifest

`manifest.txt` patches the residue the pure-LLBC scan gets wrong. Two sections:

- `[ignore]` — compiler-internal items that appear in every crate but are never
  a real gap (drop glue, marker traits). Dropped from the *used* set.
- `[covered]` — `core`/`alloc`/`std` items the library *does* provide but that
  don't name-match the model LLBC.

Paste keys **exactly** as they appear in the `MISSING` output (they are already
in normalized form).

## Known false-positive categories (triage into the manifest)

This is a compatibility *estimate*. Because the covered set is derived from the
model's LLBC rather than its final Lean library, a few categories show up as
`MISSING` even though the Lean library handles them. When you confirm one is
actually covered, add its key to `[covered]`:

- **Glue routed through `rust_primitives` / hand-written Lean.** e.g.
  `u32::leading_zeros` is modeled as a free function, not the `u32` inherent
  method, so it won't name-match. (Contrast `u32::div_ceil`, which is a *real*
  gap — genuinely not in the model.)
- **Abstract default trait methods** (`Iterator::map`, `Iterator::collect`,
  `Sum::sum`, …) the model never calls internally, so they never appear in its
  LLBC even when the Lean library provides the default.
- **Blanket vs concrete impls** — the model has `impl AsRef<T> for T` while the
  target uses `impl AsRef<[T]> for [T]`; these don't string-match even though
  the blanket impl applies.
- **Items removed via `CHARON_EXCLUDES`** and re-supplied as hand-written Lean
  (`*External.lean`).

Inspecting `MISSING` and growing `manifest.txt` is the intended workflow; over
time the false-positive list shrinks to the genuine gaps.

## The Lean-extraction check

`lean_extract_compat.py` answers the same question — *which `core`/`alloc` items
does this crate need that the model doesn't provide?* — but from the **other
end** of the pipeline: the Lean that aeneas has already emitted for the crate.

```sh
python3 tools/aeneas-compat/lean_extract_compat.py --lean-dir path/to/crate/lean
python3 tools/aeneas-compat/lean_extract_compat.py --lean-dir <dir> --json
python3 tools/aeneas-compat/lean_extract_compat.py --lean-dir <dir> --show-candidates
```

It needs a **built** `CoreModels` lake project (the repo's `lean/`, used to
resolve names; override with `--core-models-lean`). It does *not* need charon or
aeneas — only the crate's already-extracted `.lean` files.

### Why it's more precise

The extracted `Funs.lean` / `Types.lean` reference `core`/`alloc` as the exact
mangled identifiers aeneas chose (e.g.
`core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map`).
Reading them directly avoids *reconstructing* those names, so none of aeneas'
mangling subtleties can produce a false positive.

It is also better than just running `lake build` and reading the errors:

- **deduplicated** — a missing name used at 10 sites is reported once, not ten
  times;
- **no cascade noise** — a build emits unrelated type errors once a definition
  fails; this tool only ever reports unknown `core`/`alloc` names;
- **strictly more complete** — once a definition fails on its first unknown
  identifier, the build *masks* the remaining unknowns in that definition; this
  tool sees them all (on `tests/list_coverage` it surfaces 5 genuine gaps the
  build never prints).

### How it works

1. Scan the crate's `.lean` files for referenced `core.*` / `alloc.*` names and
   for the names the crate *defines itself*.
2. Drop any reference whose name — or any ancestor prefix — is self-defined.
   This is the Lean-level analogue of charon's `is_local`: test crates that
   mirror std paths (e.g. `tests/rust_lean_equiv_test`) emit their own functions
   and lifted closures under literal `core.*` / `alloc.*` namespaces, which are
   textually indistinguishable from real `core` references.
3. Resolve the survivors against `CoreModels` with `check_lean_missing.lean`.
   Resolution uses the **elaborator**, so a dot-notation projection on an
   instance term (`<instance>.partial_cmp`) counts as covered even though it is
   not itself a standalone constant — exactly as it would during a real build.

Validated against `lake build` on the bundled test crates: **zero false
negatives** (it never clears a name the build rejects), `0` missing on the two
crates that build clean (`client_test`, `rust_lean_equiv_test`), and a
deduplicated, build-masking-aware gap list on `list_coverage`.

## Planned extensions

The `--json` output is the foundation for:

1. emitting a `.lean` file declaring the missing items as axioms with their
   reconstructed types (needs type reconstruction from the target LLBC);
2. emitting `charon --exclude` flags (and/or a list of the target's
   modules/items) that carve out an analyzable subset touching only covered
   features.
