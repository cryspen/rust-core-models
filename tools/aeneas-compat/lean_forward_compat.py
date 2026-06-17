#!/usr/bin/env python3
"""PROTOTYPE: compat estimate by FORWARD-naming Rust items into Lean names.

Strategy (vs the LLBC-based `aeneas_compat.py`):
  1. Enumerate the Lean declarations actually present in the `CoreModels`
     library (via `dump_lean_names.lean`) — this is the ground-truth "covered"
     set and, crucially, includes the HAND-WRITTEN Lean (scalar instances,
     epilogue defs, …) that the model's LLBC does not contain.
  2. For each `core`/`alloc`/`std` item the target crate uses (from charon),
     apply aeneas's naming rules FORWARD to produce the Lean name(s) that item
     would resolve to, and check membership in the set from (1).

Forward (Rust -> Lean) is preferred over backward (Lean -> Rust) because
aeneas's name mangling is a deterministic function but not cleanly invertible:
`CoreCmpPartialEqU8` cannot be unambiguously split back into
`core::cmp::PartialEq<u8>` without a dictionary, but producing it forward is
unambiguous.

This is a PROTOTYPE: the forward namer covers the common shapes (plain
types/functions, trait-method projections, scalar inherent methods, trait
impls via a small trait-path dictionary). Items it can't map are reported as
"unmapped" rather than silently counted, so the mapper's reach is visible.
"""
from __future__ import annotations
import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

# reuse the charon extraction from the sibling tool
sys.path.insert(0, str(Path(__file__).resolve().parent))
import aeneas_compat as ac  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# Lean scalar / primitive type names (Rust -> aeneas Lean spelling).
SCALAR = {f"{s}{w}": f"{s.upper()}{w}"
          for s in ("u", "i") for w in (8, 16, 32, 64, 128)}
SCALAR.update({"usize": "Usize", "isize": "Isize", "bool": "Bool",
               "char": "Char", "f32": "F32", "f64": "F64"})

# Lean spelling of common non-scalar self types appearing in impl blocks.
TYPE_LEAN = {"[T]": "Slice", "[T; N]": "Array", "str": "Str"}

def load_trait_paths(llbc_json: Path) -> dict[str, list[str]]:
    """Build {short trait name -> [full Rust paths]} from the crate LLBC's
    `trait_decls` (the `.llbc` is JSON). This replaces a hand-kept dictionary:
    the pretty-print only shows the abbreviated trait name inside `{impl ...}`,
    but the JSON carries every (foreign and local) trait's full path. Same-short
    collisions (e.g. two `Sealed`s) keep all candidates."""
    import json
    doc = json.loads(Path(llbc_json).read_text())
    out: dict[str, list[str]] = {}
    for td in doc.get("translated", {}).get("trait_decls", []):
        segs = [e["Ident"][0] for e in td.get("item_meta", {}).get("name", [])
                if isinstance(e, dict) and "Ident" in e]
        if segs:
            out.setdefault(segs[-1], [])
            full = "::".join(segs)
            if full not in out[segs[-1]]:
                out[segs[-1]].append(full)
    return out


def dump_lean_names(lean_dir: Path, cache: Path | None) -> set[str]:
    """Return the set of `core.*` / `alloc.*` Lean name suffixes (the
    `CoreModels.` prefix stripped)."""
    if cache and cache.exists():
        text = cache.read_text()
    else:
        script = Path(__file__).resolve().parent / "dump_lean_names.lean"
        proc = subprocess.run(["lake", "env", "lean", str(script)],
                              cwd=lean_dir, capture_output=True, text=True)
        if proc.returncode != 0:
            sys.exit(f"failed to dump Lean names (is {lean_dir} built? "
                     f"`make lean`):\n{proc.stderr}")
        text = proc.stdout
        if cache:
            cache.write_text(text)
    out = set()
    for line in text.splitlines():
        line = line.strip()
        for pre in ("CoreModels.core.", "CoreModels.alloc."):
            if line.startswith(pre):
                out.add(line[len("CoreModels."):])  # -> "core...." / "alloc...."
    return out


def _strip_generics(s: str) -> str:
    return ac._strip_generic_args(re.sub(r"'[A-Za-z0-9_]+", "", s)).strip()


def _camel(path: str) -> str:
    """core::cmp::PartialEq -> CoreCmpPartialEq."""
    return "".join(seg[:1].upper() + seg[1:]
                   for seg in path.split("::") if seg)


def _type_lean(ty: str) -> str | None:
    ty = ty.strip().lstrip("&").strip()
    ty = re.sub(r"^(mut|'[A-Za-z0-9_]+)\s+", "", ty).strip()
    if ty in SCALAR:
        return SCALAR[ty]
    if ty in TYPE_LEAN:
        return TYPE_LEAN[ty]
    base = ty.split("<", 1)[0].strip()        # Vec<T> -> Vec, Map<..> -> Map
    base = base.split("::")[-1]               # alloc::vec::into_iter::IntoIter -> IntoIter
    if re.fullmatch(r"[A-Z][A-Za-z0-9_]*", base):
        return base
    return None


def crate_local_paths(llbc_json: Path) -> set[str]:
    """De-prefixed names of the crate's OWN (is_local) items, so we can exclude
    them from the "used" set. The prefix heuristic alone misclassifies crates
    whose source is laid out under `core`/`alloc` modules (their local
    `<crate>::core::foo` items look external); is_local from the JSON is the
    authoritative signal."""
    import json
    doc = json.loads(Path(llbc_json).read_text())
    tr = doc.get("translated", {})
    out: set[str] = set()
    for table in ("fun_decls", "type_decls", "trait_decls", "global_decls"):
        for d in tr.get(table, []):
            if not isinstance(d, dict):
                continue
            im = d.get("item_meta") or {}
            if not im.get("is_local"):
                continue
            segs = [e["Ident"][0] for e in (im.get("name") or [])
                    if isinstance(e, dict) and "Ident" in e]
            if len(segs) > 1:                 # drop the crate-name segment
                out.add("::".join(segs[1:]))
    return out


def self_type_paths(lean_names: set[str]) -> dict[str, set[str]]:
    """short type name -> full Lean self-paths that carry instances. Learned
    from the dump itself, so the instance namespace is whatever aeneas actually
    used (`core.result.Result.Insts.…`, `core.U8.Insts.…`, …) rather than a
    guessed `core.<Type>`."""
    out: dict[str, set[str]] = {}
    for n in lean_names:
        if ".Insts." in n:
            self_path = n.split(".Insts.", 1)[0]
            out.setdefault(self_path.split(".")[-1], set()).add(self_path)
    return out


def is_drop_glue(rust: str) -> bool:
    """Compiler-inserted drop glue — aeneas never emits a model reference for
    it, so it is never a real coverage gap."""
    return ("drop_in_place" in rust or "::Destruct" in rust
            or rust.endswith("Destruct"))


_IMPL_RE = re.compile(r"\{impl\s+(?P<trait>.+?)\s+for\s+(?P<self>.+?)\}"
                      r"(?:::(?P<method>[A-Za-z0-9_]+))?\s*$")


def forward(rust: str, trait_paths: dict[str, list[str]],
            self_paths: dict[str, set[str]]) -> list[list[str]] | None:
    """Rust item path (charon) -> candidate Lean-name GROUPS, or None if the
    namer can't handle this shape. The item is covered iff *some* group is
    *fully* present in the Lean library (AND within a group, OR across groups).
    `trait_paths`/`self_paths` map short names to full Rust paths / Lean
    instance namespaces, both learned from data."""
    rust = rust.strip()

    # Trait impl: {impl Trait<Args> for Self}::method
    m = _IMPL_RE.search(rust)
    if m:
        trait_raw = _strip_generics(m.group("trait"))
        targs = re.findall(r"<(.*)>", m.group("trait"))
        self_lean = _type_lean(_strip_generics(m.group("self")))
        trait_short = trait_raw.split("::")[-1]
        fulls = trait_paths.get(trait_short)
        if not self_lean or not fulls:
            return None
        args_camel = ""
        if targs:
            for a in re.split(r",", targs[0]):
                al = _type_lean(_strip_generics(a))
                if al:
                    args_camel += al
        # instance namespace: prefer the self-paths aeneas actually used;
        # fall back to a constructed core./alloc. prefix.
        prefixes = self_paths.get(self_lean) or {f"core.{self_lean}",
                                                 f"alloc.{self_lean}"}
        method = m.group("method")
        groups: list[list[str]] = []
        for sp in prefixes:
            for trait_full in fulls:
                trait_lean = trait_full.replace("::", ".")  # core.cmp.PartialEq
                # aeneas is inconsistent about including trait type args in the
                # mangle; try both with and without to match either convention.
                for mangled in {_camel(trait_full), _camel(trait_full) + args_camel}:
                    inst = f"{sp}.Insts.{mangled}"
                    if method:
                        # covered if aeneas emitted a method-specific constant,
                        # OR the instance exists AND `method` is a field of the
                        # trait structure (so it resolves through the instance —
                        # true for eq/next/cmp, but NOT for default methods like
                        # `collect` that the model never defines).
                        groups.append([f"{inst}.{method}"])
                        groups.append([inst, f"{trait_lean}.{method}"])
                    else:
                        groups.append([inst])     # the instance itself
        return groups

    # Inherent method on a primitive: core::num::{u32}::wrapping_add
    m = re.search(r"^(?P<mod>(?:core|alloc|std)(?:::[A-Za-z0-9_]+)*)::"
                  r"\{(?P<self>[^}]+)\}::(?P<method>[A-Za-z0-9_]+)$",
                  _strip_generics(rust))
    if m:
        self_lean = _type_lean(m.group("self"))
        if self_lean:
            mod = m.group("mod").replace("::", ".")
            return [[f"{mod}.{self_lean}.{m.group('method')}"]]
        return None

    # Plain path: type / free fn / trait / trait-method projection.
    s = _strip_generics(rust)
    if "{" in s or "}" in s:
        return None
    segs = [seg for seg in s.split("::") if seg]
    if segs and segs[0] in ("core", "alloc", "std"):
        return [[".".join(segs)]]
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    src = ap.add_mutually_exclusive_group()
    src.add_argument("crate", nargs="?", default=".")
    src.add_argument("--llbc", type=Path)
    ap.add_argument("--lean-dir", type=Path, default=REPO_ROOT / "lean")
    ap.add_argument("--lean-names", type=Path,
                    help="pre-dumped Lean names file (else runs `lake env lean`)")
    ap.add_argument("--charon", default=os.environ.get("CHARON", "charon"))
    ap.add_argument("--show", choices=["missing", "covered", "unmapped", "all"],
                    default="missing")
    args = ap.parse_args()

    lean = dump_lean_names(args.lean_dir, args.lean_names)

    if args.llbc:
        target = args.llbc
    else:
        target = ac.run_charon_on_crate(Path(args.crate).resolve(), args.charon,
                                        os.environ.get("RUSTFLAGS", "--cfg charon"))
    names = ac.extract_names(ac.pretty_print(target, args.charon))
    locals_ = crate_local_paths(target)                     # (1) is_local filter
    used = sorted({n for n in names
                   if ac.first_segment(n) in ac.STD_CRATES
                   and ac._strip_generic_args(n) not in locals_
                   and not is_drop_glue(n)})                 # (2) drop-glue ignore
    trait_paths = load_trait_paths(target)
    self_paths = self_type_paths(lean)                       # (2) instance namespaces

    covered, missing, unmapped = [], [], []
    for r in used:
        groups = forward(r, trait_paths, self_paths)
        if groups is None:
            unmapped.append(r)
        elif any(all(n in lean for n in g) for g in groups):
            covered.append(r)
        else:
            missing.append((r, groups[0][-1]))   # representative expected name

    mapped = len(covered) + len(missing)
    print(f"target:           {args.llbc or Path(args.crate).resolve()}")
    print(f"lean names loaded: {len(lean)}")
    print(f"used core/alloc/std items: {len(used)}")
    print(f"  mapped by forward namer: {mapped}  (covered {len(covered)} / "
          f"missing {len(missing)})")
    print(f"  unmapped (namer gap):    {len(unmapped)}")

    if args.show in ("covered", "all"):
        print("\n=== COVERED (Rust -> Lean name found) ===")
        for r in covered:
            print(f"  {r}")
    if args.show in ("missing", "all"):
        print("\n=== MISSING (forward Lean name absent) ===")
        for r, ln in missing:
            print(f"  {r}\n      -> {ln}")
    if args.show in ("unmapped", "all"):
        print("\n=== UNMAPPED (forward namer can't handle this shape yet) ===")
        for r in unmapped:
            print(f"  {r}")


if __name__ == "__main__":
    main()
