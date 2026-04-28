# rust-core-models

A model of Rust's `core` and `alloc` libraries, packaged as:

1. **Rust crates** (`core-models`, `alloc`, `rust_primitives`) that mirror the
   `core::*` and `alloc::*` items downstream verified-Rust code uses.
2. A **Lean library** (`Aeneas`) extracted from those crates by
   [Aeneas](https://github.com/AeneasVerif/aeneas), suitable for
   downstream Aeneas-extracted Lean projects to depend on as a drop-in
   `core` model.
3. A **regression-test crate** (`tests/`) that exercises items from
   `core::*` / `std::*` and from the local `core_models::*` source.
   Aeneas extracts it with no post-processing — every shim it depends on
   lives in the `Aeneas` library — so this crate doubles as proof that
   downstream code can use the library `import Aeneas` and nothing else.

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
├── tests/                 # regression-test crate (core::*, std::*,
│                          #   core_models::*); extracted unmodified
├── patch_lean.py          # post-processes Aeneas's output of the
│                          #   parent library to match our package layout
│                          #   (see comment block at top)
├── Makefile               # extraction + build orchestration
└── .github/workflows/ci.yml
```

## Building

### Prerequisites

- Rust toolchain pinned by `rust-toolchain.toml`.
- `charon` and `aeneas` on `PATH` (the upstream nix flakes are the
  recommended build path; CI uses `nix build github:AeneasVerif/{charon,aeneas}`).
  Override the Makefile lookup with `make CHARON=/path/to/charon AENEAS=/path/to/aeneas`.
- [`elan`](https://github.com/leanprover/elan) for Lean.

### Targets

```sh
make lean           # extract Rust → Lean, patch, build the Aeneas library
make tests          # regression test crate (./tests)

make clean          # remove all generated Lean + LLBC, keep hand-written
```

`make lean` is idempotent: re-running without source changes is a no-op
modulo Lake's incremental build.

## Using the Lean library downstream

Add to your downstream `lakefile.toml`:

```toml
[[require]]
name = "CoreModels"
git = "https://github.com/<owner>/rust-core-models"
rev = "<tag-or-sha>"
subDir = "lean"
```

Then `import CoreModels` in your generated Lean files. Aeneas-extracted code
that uses `std::*` types will resolve through this library's
`core.*` / `alloc.*` shims.

## Testing methodology

`tests/src/lib.rs` mixes both directions in one crate:

- Calls into `core::*` / `std::*` (e.g. `Vec::push`, `Option::unwrap_or`,
  `core::mem::swap`) — exercises Aeneas's builtin name map routing
  references to the Lean shims we provide.
- Calls that pass through the local `core_models::*` source as charon
  sees it — exercises the round-trip from our Rust source through
  extraction to the same Lean shims.

The crate is extracted with vanilla `aeneas` and built directly against
`Aeneas` — no `patch_lean.py` post-processing. Anything required to
make that work lives in the `Aeneas` library itself. CI runs the full
extraction + Lake build on every PR.

## Known gaps

- `core::slice::index::SliceIndex` and the trait impls are excluded from
  extraction (see `CHARON_EXCLUDES` in `Makefile`). Modeling the full
  trait would require `Sealed` super-trait + `&mut` back-edge tuples for
  `get_mut`/`index_mut` + raw-pointer plumbing for `get_unchecked*`.
  Tracked as TODO in `lean/Aeneas/StdAliases.lean` and the
  commented-out blocks in `tests/src/lib.rs`.
- A few iterator adapter `*::next` definitions are commented out by the
  patcher because Lean rejects field-projection-on-trait-method-param.
  See `FUNS_TO_REMOVE` in `patch_lean.py` for the list.

## Contributing

PRs welcome. Please:
- Run `cargo fmt --all` and `make lean tests` before opening a PR (CI
  enforces both).
- For new `core::*` / `alloc::*` items, add at least one function to
  `tests/src/lib.rs` exercising the std-side path.

## License

[fill in]
