#!/usr/bin/env python3
"""Estimate a crate's compatibility with the `CoreModels` Aeneas library.

Run this on a Rust crate *before* analyzing it with charon + aeneas to see
which `core::*` / `alloc::*` / `std::*` items the crate touches, which of those
the model in this repo covers, and which are still missing.

How it works
------------
1. **Used set** — run charon on the target crate to produce an LLBC, then
   `charon pretty-print` it and collect every fully-qualified item whose path
   starts with `core::`, `alloc::` or `std::`. Because charon has already
   desugared operators (`a == b` -> `PartialEq::eq`), resolved trait-method
   dispatch and deref coercions, this is *exactly* the external surface aeneas
   will need to resolve — far more faithful than a source-level (`syn`) scan.

2. **Covered set** — do the same on the model's own LLBCs (`core_models.llbc`,
   `alloc.llbc`). The covered set is every `core`/`alloc`/`std` item that
   appears anywhere in those LLBCs:
     - the model's *local* definitions (`core_models::*` / `alloc_models::*`),
       renamed back to `core::*` / `alloc::*`; plus
     - the *foreign* `core`/`alloc`/`std` items the model references and still
       extracts against (the Lean library is known to resolve these, since the
       model + its tests elaborate against `CoreModels` in CI).
   A small hand-maintained manifest (`manifest.txt`) patches the residue:
   glue cases routed through `rust_primitives` / hand-written Lean, and
   compiler-internal noise that is never a real gap.

3. **Missing set** = used - covered - manifest.

Items are compared on a *normalized key* that strips generic arguments,
lifetimes, and (inside `{impl ...}` blocks) path qualifiers, so that the
target's context-abbreviated names line up with the model's fully-qualified
ones.

This is a compatibility *estimate*: the normalization is intentionally coarse,
and the manifest is the escape hatch for the cases it gets wrong. Inspect the
reported `missing` list and grow `manifest.txt` accordingly.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
# tools/aeneas-compat/ -> repo root
REPO_ROOT = SCRIPT_DIR.parent.parent

# Path prefixes that denote the std-library surface we care about, in a
# *target* crate. (In a target crate, anything under these is external.)
STD_CRATES = ("core", "alloc", "std")

# Leading-segment rename: the model crates are extracted under these names but
# stand in for the real std crates.
RENAME = {"core_models": "core", "alloc_models": "alloc"}


# --------------------------------------------------------------------------- #
# charon invocation
# --------------------------------------------------------------------------- #
def run_charon_on_crate(crate_dir: Path, charon: str, rustflags: str) -> Path:
    """Run charon on a crate directory, returning the path to the LLBC."""
    out = Path(tempfile.mkstemp(suffix=".llbc", prefix="aeneas-compat-")[1])
    env = dict(os.environ)
    if rustflags:
        env.setdefault("RUSTFLAGS", rustflags)
    cmd = [charon, "cargo", "--preset=aeneas", "--dest-file", str(out)]
    proc = subprocess.run(cmd, cwd=crate_dir, env=env)
    if proc.returncode != 0:
        # charon can exit non-zero while still producing a usable LLBC.
        if not (out.exists() and out.stat().st_size > 0):
            sys.exit(f"charon failed on {crate_dir} (exit {proc.returncode}) "
                     f"and produced no LLBC")
        print(f"warning: charon exited {proc.returncode} on {crate_dir}; "
              f"using the partial LLBC it produced", file=sys.stderr)
    return out


def pretty_print(llbc: Path, charon: str) -> str:
    proc = subprocess.run([charon, "pretty-print", str(llbc)],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit(f"`charon pretty-print {llbc}` failed:\n{proc.stderr}")
    return proc.stdout


# --------------------------------------------------------------------------- #
# name extraction + normalization
# --------------------------------------------------------------------------- #
_FULL_NAME_RE = re.compile(r"//\s*Full name:\s*(.+?)\s*$")
# Inline declaration: `pub fn core::cmp::PartialEq::eq<...>(...)`, `struct X`, ...
# (trait methods print canonically inline, *without* a Full-name comment).
_DECL_RE = re.compile(
    r"^\s*(?:pub\s+)?(?:opaque\s+)?"
    r"(?:fn|struct|enum|trait|type|global|const)\s+"
    r"([^\s(<{=]+)"
)
# Any root-anchored qualified path, anywhere in the text (signatures, the
# `fn foo = core::..::method` RHS of trait bodies, etc.). Word/`::` only, so it
# stops cleanly at `<`/`(`/whitespace; `{impl ...}` names (which contain spaces)
# are instead picked up by the Full-name comments and decl headers above.
_PATH_RE = re.compile(
    r"\b(?:core|std|alloc|core_models|alloc_models|rust_primitives)"
    r"(?:::[A-Za-z0-9_]+)+"
)


def extract_names(pretty: str) -> set[str]:
    """Collect every fully-qualified item path mentioned by a pretty-print."""
    names: set[str] = set()
    for line in pretty.splitlines():
        m = _FULL_NAME_RE.search(line)
        if m:
            names.add(m.group(1))
        m = _DECL_RE.match(line)
        if m and not m.group(1).endswith(":"):
            # a trailing `::` means the path was truncated at a `{impl ...}` /
            # `{[T]}` block; the full name comes via the Full-name comment.
            names.add(m.group(1))
        names.update(_PATH_RE.findall(line))
    return _maximal(names)


def _maximal(names: set[str]) -> set[str]:
    """Drop any name that is a proper `::`-prefix of another (a module path
    captured because the regex stopped at `::{` or `<`). Keeps only the
    longest, most specific item paths."""
    prefixes: set[str] = set()
    for n in names:
        segs = n.split("::")
        for i in range(1, len(segs)):
            prefixes.add("::".join(segs[:i]))
    return {n for n in names if n not in prefixes}


def _rename_leading(name: str) -> str:
    """core_models::foo -> core::foo ; alloc_models::foo -> alloc::foo."""
    head, sep, rest = name.partition("::")
    if head in RENAME and sep:
        return RENAME[head] + "::" + rest
    return name


def _strip_generic_args(s: str) -> str:
    """Remove `<...>` generic-argument lists, but keep `<slice>`/`<array>`
    path segments (charon's notation for primitive-type impl modules).

    A `<` opens generic args only when it directly follows an identifier char
    or a closing `>` (e.g. `Map<...>`, `Foo<...><...>`); a `<` that follows
    `::`, whitespace or the start of the string is a path segment and is kept.
    """
    out: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == "<":
            prev = out[-1] if out else ""
            if prev.isalnum() or prev == "_" or prev == ">":
                # generic argument list: skip balanced <...>
                depth = 1
                i += 1
                while i < n and depth:
                    if s[i] == "<":
                        depth += 1
                    elif s[i] == ">":
                        depth -= 1
                    i += 1
                continue
        out.append(c)
        i += 1
    return "".join(out)


def _reduce_quals_in_braces(s: str) -> str:
    """Inside `{...}`, reduce `a::b::Name` runs to their last segment, so that
    `{impl core::cmp::PartialEq for u8}` and `{impl PartialEq for u8}` agree."""
    def reduce_region(region: str) -> str:
        return re.sub(r"[A-Za-z0-9_]+(?:::[A-Za-z0-9_]+)+",
                      lambda m: m.group(0).rsplit("::", 1)[-1],
                      region)

    out: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        if s[i] == "{":
            depth = 1
            j = i + 1
            while j < n and depth:
                if s[j] == "{":
                    depth += 1
                elif s[j] == "}":
                    depth -= 1
                j += 1
            out.append("{" + reduce_region(s[i + 1:j - 1]) + "}")
            i = j
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def normalize(name: str) -> str:
    s = _rename_leading(name)
    s = re.sub(r"'[A-Za-z0-9_]+", "", s)   # strip lifetimes
    s = _strip_generic_args(s)
    s = _reduce_quals_in_braces(s)
    s = re.sub(r"\s+", " ", s).strip()
    s = re.sub(r"\s*::\s*", "::", s)
    return s


def ident_key(name: str) -> str:
    """Module-independent identity key used for matching.

    The model frequently authors an impl in a different module than real core
    (e.g. `impl Default for u8` lives in `core_models::num`, not
    `core::default`). A trait impl's identity is `{impl Trait for Type}::method`
    regardless of where it is written, so for any name containing an `{impl ...}`
    block we drop the authoring module path and key on the impl block (with
    trait/type reduced to bare names) plus the trailing method. Everything else
    (free functions, types, trait declarations and their abstract methods) keeps
    its full, renamed module path."""
    s = normalize(name)
    i = s.rfind("{impl")
    return s[i:] if i != -1 else s


def first_segment(name: str) -> str:
    return name.split("::", 1)[0].split("<", 1)[0].strip()


def _degenerate(key: str) -> bool:
    """A key that is empty, ends in `::`, or has an empty path segment is a
    truncation artifact, not a real item."""
    return (not key) or key.endswith("::") or "" in key.split("::")


# --------------------------------------------------------------------------- #
# manifest
# --------------------------------------------------------------------------- #
def load_manifest(path: Path) -> dict[str, set[str]]:
    """Tiny line-based format:  [section] headers, one item per line, # comments.

    Sections:
      [covered]  normalized keys to treat as covered (glue / hand-written Lean).
      [ignore]   normalized keys to drop from the *used* set entirely
                 (compiler-internal noise that is never a real gap).
    Lines are matched against the *normalized* key, so paste keys exactly as
    they appear in this tool's `missing` output.

    A line containing `*` is a glob (fnmatch) against the normalized key, so a
    single `*{impl Destruct for *}::drop_in_place` covers all drop glue.
    """
    sections = {"covered": {"exact": set(), "globs": []},
                "ignore": {"exact": set(), "globs": []}}
    if not path.exists():
        return sections
    cur = None
    for raw in path.read_text().splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r"\[(\w+)\]$", line)
        if m:
            cur = m.group(1)
            sections.setdefault(cur, {"exact": set(), "globs": []})
            continue
        if cur is not None:
            if "*" in line:
                sections[cur]["globs"].append(normalize(line))
            else:
                sections[cur]["exact"].add(ident_key(line))
    return sections


def _manifest_match(key: str, section: dict) -> bool:
    if key in section["exact"]:
        return True
    return any(fnmatch.fnmatchcase(key, g) for g in section["globs"])


# --------------------------------------------------------------------------- #
# core logic
# --------------------------------------------------------------------------- #
def relevant_used(names: set[str]) -> dict[str, set[str]]:
    """ident-key -> original names, for target items under core/alloc/std."""
    by_key: dict[str, set[str]] = {}
    for nm in names:
        if first_segment(nm) in STD_CRATES:
            key = ident_key(nm)
            if _degenerate(key):
                continue
            by_key.setdefault(key, set()).add(nm)
    return by_key


def covered_keys(names: set[str]) -> set[str]:
    """ident-keys the model provides: any core/alloc/std item it mentions or
    defines (local `*_models` defs are renamed first, so they land under
    core/alloc)."""
    keys: set[str] = set()
    for nm in names:
        renamed = _rename_leading(nm)
        if first_segment(renamed) in STD_CRATES:
            keys.add(ident_key(renamed))
    return keys


def group_by_module(keys: set[str]) -> dict[str, list[str]]:
    groups: dict[str, list[str]] = {}
    for k in sorted(keys):
        segs = k.split("::")
        mod = "::".join(segs[:3]) if len(segs) >= 3 else "::".join(segs[:2])
        groups.setdefault(mod, []).append(k)
    return groups


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Estimate a crate's compatibility with the CoreModels "
                    "Aeneas library.")
    src = ap.add_mutually_exclusive_group()
    src.add_argument("crate", nargs="?", default=".",
                     help="path to the target crate dir (default: cwd)")
    src.add_argument("--llbc", type=Path,
                     help="use a pre-built target LLBC instead of running charon")
    ap.add_argument("--model-llbc", type=Path,
                    default=REPO_ROOT / "core_models.llbc")
    ap.add_argument("--alloc-llbc", type=Path,
                    default=REPO_ROOT / "alloc.llbc")
    ap.add_argument("--manifest", type=Path, default=SCRIPT_DIR / "manifest.txt")
    ap.add_argument("--charon", default=os.environ.get("CHARON", "charon"))
    ap.add_argument("--rustflags", default=os.environ.get("RUSTFLAGS", "--cfg charon"),
                    help="RUSTFLAGS for the target charon run (default: --cfg charon)")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--show-covered", action="store_true",
                    help="also list the covered items")
    ap.add_argument("--no-manifest", action="store_true",
                    help="ignore the manifest (show raw auto-derived result)")
    args = ap.parse_args()

    # --- model / covered set ---
    model_llbcs = [p for p in (args.model_llbc, args.alloc_llbc) if p and p.exists()]
    if not model_llbcs:
        sys.exit(f"no model LLBCs found (looked for {args.model_llbc}, "
                 f"{args.alloc_llbc}). Run `make llbc alloc-llbc` in {REPO_ROOT}.")
    covered: set[str] = set()
    for llbc in model_llbcs:
        covered |= covered_keys(extract_names(pretty_print(llbc, args.charon)))

    manifest = {"covered": {"exact": set(), "globs": []},
                "ignore": {"exact": set(), "globs": []}}
    if not args.no_manifest:
        manifest = load_manifest(args.manifest)
    covered |= manifest["covered"]["exact"]

    # --- target / used set ---
    if args.llbc:
        target_llbc = args.llbc
        if not target_llbc.exists():
            sys.exit(f"target LLBC not found: {target_llbc}")
    else:
        target_llbc = run_charon_on_crate(Path(args.crate).resolve(),
                                           args.charon, args.rustflags)
    used = relevant_used(extract_names(pretty_print(target_llbc, args.charon)))

    # drop manifest-ignored noise
    for key in list(used):
        if _manifest_match(key, manifest["ignore"]):
            del used[key]

    # Every remaining used item is either covered (by the model LLBC scan or by
    # a manifest assertion) or missing — a clean partition, so
    # used == covered + missing. (The [ignore] items were already removed from
    # `used` above, so they sit outside this partition by construction.)
    covered_used = {k for k in used
                    if k in covered or _manifest_match(k, manifest["covered"])}
    missing_keys = set(used) - covered_used

    if args.json:
        out = {
            "target": str(args.llbc or args.crate),
            "used_count": len(used),
            "covered_count": len(covered_used),
            "missing_count": len(missing_keys),
            "missing": sorted(missing_keys),
            "covered": sorted(covered_used),
            "originals": {k: sorted(v) for k, v in used.items()},
        }
        print(json.dumps(out, indent=2))
        return

    print(f"target:  {args.llbc or Path(args.crate).resolve()}")
    print(f"model:   {', '.join(str(p) for p in model_llbcs)}")
    print()
    print(f"used core/alloc/std items: {len(used)}")
    print(f"  covered by library:      {len(covered_used)}")
    print(f"  MISSING:                 {len(missing_keys)}")
    print()
    if missing_keys:
        print("=== MISSING (not provided by the library) ===")
        for mod, keys in group_by_module(missing_keys).items():
            print(f"\n# {mod}")
            for k in keys:
                print(f"  {k}")
        print("\nIf any of the above is a false positive (covered by "
              "hand-written Lean / rust_primitives glue, or compiler-internal "
              f"noise), add it to:\n  {args.manifest}")
    else:
        print("All used items are covered by the library. ✓")

    if args.show_covered and covered_used:
        print("\n=== COVERED ===")
        for mod, keys in group_by_module(covered_used).items():
            print(f"\n# {mod}")
            for k in keys:
                print(f"  {k}")


if __name__ == "__main__":
    main()
