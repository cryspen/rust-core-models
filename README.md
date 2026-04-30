# rust-core-models

A model of Rust's `core` and `alloc` libraries, packaged as:

1. **Rust crates** (`core-models`, `alloc`, `rust_primitives`) that mirror the
   `core::*` and `alloc::*` items downstream verified-Rust code uses.
2. A **Lean library** (`CoreModels`) extracted from those crates by
   [Aeneas](https://github.com/AeneasVerif/aeneas), suitable for
   downstream Aeneas-extracted Lean projects to depend on as a drop-in
   `core` model.
3. A **regression-test crate** (`tests/`) that exercises items from
   `core::*` / `std::*`.

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
`lean/CoreModels/{Funs,Types,…}.lean` match what a fresh extraction produces
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
│   └── CoreModels/        # hand-written + extracted, both committed
├── tests/                 # regression-test crate (core::*, std::*)
├── patch_lean.py          # post-processes Aeneas's output of the
│                          #   parent library to match our package layout
│                          #   (see comment block at top of the file)
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
git = "https://github.com/cryspen/rust-core-models"
rev = "COMMIT_HASH_HERE"
subDir = "lean"
```

Then `import CoreModels` in your generated Lean files and replace the line
```
open Aeneas Aeneas.Std Result ControlFlow Error
```
by
```
open core_models Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
```
Then the Aeneas-extracted code that uses `std::*` types will resolve through this library's
`core.*` / `alloc.*` shims.

## Contributing

PRs welcome. Please:
- Run `cargo fmt --all` and `make lean tests` before opening a PR (CI
  enforces both).
- For new `core::*` / `alloc::*` items, add at least one function to
  `tests/src/lib.rs` exercising the std-side path.

## License

[fill in]
