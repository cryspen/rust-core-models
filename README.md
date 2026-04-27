# rust-core-models

A model of Rust's `core` and `alloc` libraries, packaged as:

1. **Rust crates** (`core-models`, `alloc`, `rust_primitives`) that mirror the
   `core::*` and `alloc::*` items downstream verified-Rust code uses.
2. A **Lean library** (`Aeneas`) extracted from those crates by
   [Aeneas](https://github.com/AeneasVerif/aeneas), suitable for
   downstream Aeneas-extracted Lean projects to depend on as a drop-in
   `core` model.
3. **Test infrastructure** that exercises both the extraction
   (`test-suite/`) and downstream consumption via Aeneas's name map
   (`aeneas-test/`) — both must stay green before a release.

## Why this exists

Verified-Rust pipelines need a model of `core` and `alloc` to elaborate
against. Writing that model in Rust (rather than directly in each
verification tool's logic) has three advantages:

- **Easy to extend**: adding a new `core::*` item is just a Rust source
  edit, no proof-assistant boilerplate.
- **Cross-testable against the real Rust core library**: the model is
  ordinary Rust, so we can compile and run it side-by-side with `std`
  and check behavioral agreement.
- **Shareable across verification tools**: a single Rust model feeds
  multiple downstream backends — currently hax-F\*, hax-Lean, and
  Aeneas-Lean — instead of each tool maintaining its own shadow `core`.

CI verifies that the *committed* extracted Lean files in
`lean/Aeneas/{Funs,Types,…}.lean` match what a fresh extraction produces
against the pinned toolchain. That means a downstream Lean consumer can
just `lake update` this repo without installing the Rust toolchain.

## Repository layout

```
.
├── core-models/           # main Rust crate: model of `core::*`
├── alloc/                 # model of `alloc::*` (separate crate so it
│                          #   can be extracted with charon's
│                          #   `alloc_models` rename trick — see Makefile)
├── rust_primitives/       # tiny crate of helpers (slice/array primitives)
├── lean/                  # the distributed Lean library
│   ├── lakefile.toml
│   ├── lean-toolchain
│   └── Aeneas/            # hand-written + extracted, both committed
├── test-suite/            # extraction-side regression: core_models::* → Lean
├── aeneas-test/           # consumption-side regression: std::* → Lean
│                          #   via Aeneas's name map
├── patch_lean.py          # post-processes Aeneas's output to match our
│                          #   package layout (see comment block at top)
├── Makefile               # extraction + build orchestration
└── .github/workflows/ci.yml
```

## Building

### Prerequisites

- Rust toolchain pinned by `rust-toolchain.toml`.
- `charon` and `aeneas` built from source at the pinned SHAs. Default
  Makefile expects them under `$HOME/cryspen/aeneas/{charon/bin,bin}`;
  override with `make CHARON=… AENEAS=…` or `make AENEAS_DIR=…`.
- [`elan`](https://github.com/leanprover/elan) for Lean.

### Targets

```sh
make lean           # extract Rust → Lean, patch, build the Aeneas library
make test-suite     # extraction-side regression (./test-suite)
make aeneas-test    # consumption-side regression (./aeneas-test)

make clean          # remove all generated Lean + LLBC, keep hand-written
```

`make lean` is idempotent: re-running without source changes is a no-op
modulo Lake's incremental build.

## Using the Lean library downstream

Add to your downstream `lakefile.toml`:

```toml
[[require]]
name = "Aeneas"
git = "https://github.com/<owner>/rust-core-models"
rev = "<tag-or-sha>"
subDir = "lean"
```

Then `import Aeneas` in your generated Lean files. Aeneas-extracted code
that uses `std::*` types will resolve through this library's
`core.*` / `alloc.*` shims.

## Testing methodology

Two regression crates exercise orthogonal directions:

- **`test-suite/`** uses items from the local `core_models` source (e.g.
  `core_models::option::Option::unwrap_or`). Catches breakage when you
  change a Rust source file.
- **`aeneas-test/`** uses `std::*` types directly (e.g. `Option<u8>`,
  `Vec<u32>`, `&[u8]`). Catches breakage in our Lean shims that arises
  only when downstream Aeneas extraction routes a `std::*` reference
  through its builtin name map to a Lean symbol we provide.

Run both before tagging a release. Both must be green. CI does this
automatically on every PR.

## Known gaps

- `core::slice::index::SliceIndex` and the trait impls are excluded from
  extraction (see `CHARON_EXCLUDES` in `Makefile`). Modeling the full
  trait would require `Sealed` super-trait + `&mut` back-edge tuples for
  `get_mut`/`index_mut` + raw-pointer plumbing for `get_unchecked*`.
  Tracked as TODO in `lean/Aeneas/StdAliases.lean` and the
  commented-out blocks in `aeneas-test/src/lib.rs`.
- A few iterator adapter `*::next` definitions are commented out by the
  patcher because Lean rejects field-projection-on-trait-method-param.
  See `FUNS_TO_REMOVE` in `patch_lean.py` for the list.

## Contributing

PRs welcome. Please:
- Run `cargo fmt --all` and `make lean test-suite aeneas-test` before
  opening a PR (CI enforces both).
- For new `core::*` / `alloc::*` items, add at least one function to
  `aeneas-test/src/lib.rs` exercising the std-side path.

## License

[fill in]
