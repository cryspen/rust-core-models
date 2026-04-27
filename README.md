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

Verified-Rust pipelines (hax → Aeneas → Lean) need a Lean shadow of `core`
and `alloc` to elaborate against. Aeneas ships its own model that depends
on a full mathlib stack; this repo provides a leaner, focused alternative
that's easier to vendor into smaller projects.

## Toolchain matrix

Bump any one of these as a single PR and update the row below.

| Component                              | Version / SHA                                 |
|----------------------------------------|-----------------------------------------------|
| Rust toolchain                         | `nightly-2026-02-07`                          |
| [charon](https://github.com/AeneasVerif/charon) | [`c0965bbc`](https://github.com/AeneasVerif/charon/commit/c0965bbccdbd87d494b240a4274707356ef0cb88) |
| [aeneas](https://github.com/AeneasVerif/aeneas) | [`3c9b4907`](https://github.com/AeneasVerif/aeneas/commit/3c9b490747294eb39a6e830930d44b5902c60d39) |
| Lean toolchain                         | `leanprover/lean4:v4.29.0-rc1`                |
| mathlib (transitive via Aeneas)        | resolved by Aeneas's `lake-manifest.json`     |
| [hax](https://github.com/cryspen/hax)  | [`492a34e3`](https://github.com/cryspen/hax/commit/492a34e33c8744b9672eb3cf1c982ac40469f7d4) |

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

- Rust toolchain pinned by `rust-toolchain.toml` (see matrix above).
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
- Update the toolchain matrix if you bump any pinned version.
- For new `core::*` / `alloc::*` items, add at least one function to
  `aeneas-test/src/lib.rs` exercising the std-side path.

## License

[fill in]
