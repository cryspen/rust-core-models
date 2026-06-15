# aeneas-compat

Estimate a crate's compatibility with the `CoreModels` Aeneas library *before*
you try to analyze it with charon + aeneas.

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

## Planned extensions

The `--json` output is the foundation for:

1. emitting a `.lean` file declaring the missing items as axioms with their
   reconstructed types (needs type reconstruction from the target LLBC);
2. emitting `charon --exclude` flags (and/or a list of the target's
   modules/items) that carve out an analyzable subset touching only covered
   features.
