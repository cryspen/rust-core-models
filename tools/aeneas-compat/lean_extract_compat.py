#!/usr/bin/env python3
"""Find the core/alloc items an Aeneas-extracted crate needs but CoreModels lacks.

This works at the *Lean* level, the opposite altitude from ``aeneas_compat.py``
(which works at the charon LLBC level) and ``lean_forward_compat.py`` (which
reconstructs Lean names from Rust names). Here we read the names Aeneas
*actually emitted* into the crate's extracted ``.lean`` files and ask the
``CoreModels`` library, via the elaborator, which of them fail to resolve.

Why this beats the alternatives:

* vs. forward-naming — no name *reconstruction*, so none of aeneas' mangling
  subtleties (ref encodings, dropped generic args, inherent-method rewrites) can
  produce a false positive. We compare the emitted names directly.
* vs. ``lake build`` — a full build (a) reports *unrelated* cascade errors once a
  definition fails, (b) reports the same missing name once per use site, and
  (c) *masks* secondary unknown identifiers inside a definition that already
  failed on an earlier one. This tool is deduplicated, noise-free, and strictly
  *more* complete than the build (it sees the masked gaps too).

Pipeline:

1. Scan the crate's extracted ``.lean`` files for referenced ``core.*`` /
   ``alloc.*`` names and for the names the crate *defines itself*.
2. Drop any reference that is the crate's own item — i.e. it, or any ancestor
   prefix, is self-defined. (Test crates that mirror std module paths, like
   ``tests/rust_lean_equiv_test``, emit their own functions under literal
   ``core.*`` / ``alloc.*`` namespaces; this is the Lean-level analogue of
   charon's ``is_local`` flag.)
3. Hand the surviving candidates to ``check_lean_missing.lean``, which resolves
   each against ``CoreModels`` and prints the ones that don't resolve.

Usage:
    python3 tools/aeneas-compat/lean_extract_compat.py --lean-dir tests/list_coverage/lean
    python3 tools/aeneas-compat/lean_extract_compat.py --lean-dir <dir> --json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# A complete dotted name starting at a `core.` / `alloc.` segment. The
# look-behind forbids a preceding identifier char or dot, so we only match the
# *start* of a name — `rust_lean_tests.core.array.foo` does NOT match at `core`.
_REF = re.compile(r"(?<![\w.])(core|alloc)\.[A-Za-z0-9_.]+")

# A Lean declaration header; captures the declared (namespace-relative) name.
_DECL = re.compile(
    r"^\s*(?:noncomputable\s+|private\s+|partial\s+|@\[[^\]]*\]\s*)*"
    r"(?:def|abbrev|structure|inductive|class|instance|opaque|theorem)\s+"
    r"([A-Za-z0-9_.]+)"
)


def _ancestor_prefixes(name: str) -> list[str]:
    parts = name.split(".")
    return [".".join(parts[:i]) for i in range(1, len(parts))]


def strip_comments(text: str) -> str:
    """Blank out Lean comments and string literals, preserving line structure.

    Aeneas emits `Source:`/doc comments that mention Rust paths; without this a
    `core.`-looking token inside a comment (or string) would be a false
    reference. Handles nested `/- -/` blocks (incl. `/-- -/` docs), `--` line
    comments, and `"..."` strings. Newlines are kept so per-line `def` headers
    still parse.
    """
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    in_str = False
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if depth > 0:                       # inside a block comment
            if two == "/-":
                depth += 1; i += 2; continue
            if two == "-/":
                depth -= 1; i += 2; continue
            out.append("\n" if c == "\n" else " ")
            i += 1; continue
        if in_str:
            out.append(c)                   # keep newlines/positions; blanking optional
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1]); i += 2; continue
            if c == '"':
                in_str = False
            else:
                out[-1] = "\n" if c == "\n" else " "
            i += 1; continue
        if two == "/-":
            depth += 1; i += 2; continue
        if two == "--":
            while i < n and text[i] != "\n":  # line comment to EOL
                i += 1
            continue
        if c == '"':
            in_str = True; out.append(" "); i += 1; continue
        out.append(c); i += 1
    return "".join(out)


def scan(lean_files: list[Path]) -> tuple[set[str], set[str]]:
    """Return (referenced core/alloc names, names the crate defines itself)."""
    refs: set[str] = set()
    selfdef: set[str] = set()
    for f in lean_files:
        text = strip_comments(f.read_text())
        for line in text.splitlines():
            m = _DECL.match(line)
            if m:
                selfdef.add(m.group(1))
            for t in _REF.finditer(line):
                refs.add(t.group(0))
    return refs, selfdef


def candidates(refs: set[str], selfdef: set[str]) -> list[str]:
    """References minus the crate's own items (self-defined, incl. by ancestor)."""
    def is_local(r: str) -> bool:
        return r in selfdef or any(p in selfdef for p in _ancestor_prefixes(r))
    return sorted(r for r in refs if not is_local(r))


def resolve_missing(cands: list[str], core_models_lean: Path, checker: Path) -> list[str]:
    """Run the Lean resolver; return the candidates that don't resolve."""
    if not cands:
        return []
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
        fh.write("\n".join(cands) + "\n")
        cand_path = fh.name
    try:
        env = dict(os.environ, CANDS=cand_path)
        proc = subprocess.run(
            ["lake", "env", "lean", str(checker.resolve())],
            cwd=core_models_lean,
            env=env,
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            sys.stderr.write(proc.stderr)
            raise SystemExit(
                f"error: the Lean resolver failed (exit {proc.returncode}). "
                f"Is '{core_models_lean}' a built CoreModels lake project?"
            )
        out = [l.strip() for l in proc.stdout.splitlines() if l.strip()]
        # Keep only candidate names (defensive against any stray diagnostic text).
        cand_set = set(cands)
        return sorted(x for x in out if x in cand_set)
    finally:
        os.unlink(cand_path)


def find_lean_files(lean_dir: Path) -> list[Path]:
    return sorted(
        p for p in lean_dir.rglob("*.lean")
        if ".lake" not in p.parts
    )


def main() -> None:
    here = Path(__file__).resolve().parent
    repo_root = here.parent.parent
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean-dir", required=True, type=Path,
                    help="the crate's extracted Lean directory (scanned recursively, "
                         "skipping .lake)")
    ap.add_argument("--core-models-lean", type=Path, default=repo_root / "lean",
                    help="path to the built CoreModels lake project (default: <repo>/lean)")
    ap.add_argument("--checker", type=Path, default=here / "check_lean_missing.lean",
                    help="the Lean resolver script")
    ap.add_argument("--json", action="store_true", help="emit JSON")
    ap.add_argument("--show-candidates", action="store_true",
                    help="also print every external core/alloc name considered")
    args = ap.parse_args()

    lean_files = find_lean_files(args.lean_dir)
    if not lean_files:
        raise SystemExit(f"error: no .lean files under '{args.lean_dir}'")

    refs, selfdef = scan(lean_files)
    cands = candidates(refs, selfdef)
    missing = resolve_missing(cands, args.core_models_lean, args.checker)
    covered = sorted(set(cands) - set(missing))

    if args.json:
        print(json.dumps({
            "lean_dir": str(args.lean_dir),
            "used": len(cands),
            "covered": len(covered),
            "missing": missing,
        }, indent=2))
        return

    print(f"crate Lean: {args.lean_dir}")
    print(f"  external core/alloc names used: {len(cands)}")
    print(f"  covered by CoreModels:          {len(covered)}")
    print(f"  MISSING:                        {len(missing)}")
    if args.show_candidates:
        print("\n-- used --")
        for c in cands:
            print(f"  {'   ' if c in missing else 'ok '} {c}")
    if missing:
        print("\n-- MISSING (genuine gaps) --")
        for m in missing:
            print(f"  {m}")


if __name__ == "__main__":
    main()
