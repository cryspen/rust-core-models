#!/usr/bin/env python3
"""
Post-process Aeneas-generated Lean files into the layout expected by our
Aeneas core replacement library.

For `core_models`, Aeneas writes the following files into ./lean/ :
    Funs.lean
    Types.lean
    FunsExternal_Template.lean
    TypesExternal_Template.lean
    
For `alloc`, Aeneas writes the following files into ./lean/CoreModels/Alloc :
    Funs.lean
    Types.lean
    FunsExternal_Template.lean
    TypesExternal_Template.lean

This script:
  * Moves the files generated from `core_model` into ./lean/CoreModels/.
  * Rewrites imports & opens to match our package layout.
  * Renames `namespace core_models` -> `namespace CoreModels.core`.
    and `namespace alloc` -> `namespace CoreModels.alloc`.
  * Comments out the type-level items that we forward-declare
    in `TypesPrologue.lean`.
  * Comments out a small number of generated function definitions that have
    known elaboration issues.
  * Fixes some other elaboration issues via search and replace.

Pure-fn duplicates of `core::option::Option::{is_some, is_none, unwrap_or,
take}`, `core::mem::{swap, replace}` and the `core::num::*::{wrapping_*,
saturating_*, rotate_*, overflowing_*}` arithmetic helpers are stripped at
the LLBC level by charon's `--exclude` flag (see `CHARON_EXCLUDES` in the
parent `Makefile`), not by this script.
"""

from __future__ import annotations
import os
import re
import shutil
import sys
from pathlib import Path

LEAN_DIR = Path(__file__).parent / "lean"
CORE_DIR = LEAN_DIR / "CoreModels"
ALLOC_DIR = CORE_DIR / "Alloc"

# files to move from `lean/` into `lean/CoreModels/`
GENERATED_FILES = [
    "Funs.lean",
    "Types.lean",
    "FunsExternal_Template.lean",
    "TypesExternal_Template.lean",
]

# Type declarations in Types.lean to comment out (provided by TypesPrologue.lean)
TYPES_TO_REMOVE = [
    "core_models::clone::Clone",
    "core_models::marker::Copy",
    "core_models::ops::function::FnOnce",
    "core_models::ops::function::FnMut",
    "core_models::ops::function::Fn",
    "core_models::cmp::Ordering",
    "core_models::option::Option",
    "core_models::result::Result",
]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def read(path: Path) -> str:
    return path.read_text()


def write(path: Path, contents: str) -> None:
    path.write_text(contents)


def rewrite_imports_and_opens(text: str) -> str:
    """Rewrite `imports` and `open` to match our package layout."""
    # import
    text = re.sub(
        r"^import Aeneas$",
        "import Aeneas\nimport CoreModels.Command\nimport CoreModels.TypesPrologue",
        text, flags=re.MULTILINE,
    )
    
    # Fix the `open`s: We want to open the Aeneas library definitions, except for
    # `core` and `alloc`.
    text = re.sub(
        r"^open Aeneas Aeneas\.Std Result ControlFlow Error$",
        "open Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen Result ControlFlow Error",
        text, flags=re.MULTILINE,
    )
    return text


def rename_namespace(text: str) -> str:
    text = re.sub(r"^namespace core_models$", "namespace CoreModels.core",
                  text, flags=re.MULTILINE)
    text = re.sub(r"^end core_models$", "end CoreModels.core",
                  text, flags=re.MULTILINE)
    # Drop `open core_models` from external template files
    text = re.sub(r"^open core_models$", "-- open core_models removed",
                  text, flags=re.MULTILINE)
    return text


def fix_fail_panic(text: str) -> str:
    """In the definition of a Lean `item` called `panic`, the name `panic`
    does not resolve to `Error.panic` as it should."""
    return text.replace("  fail panic\n", "  fail Error.panic\n")


def rename_alloc_models(text: str) -> str:
    """Rewrite every occurrence of the staged crate name back to `alloc`.
    
    `core-models/alloc/` is a Rust crate named `alloc`. Aeneas's builtin path
    map already has entries for `alloc::vec::Vec`, `alloc::boxed::Box`, etc.,
    so extracting the crate as-is collides on those names and crashes the type
    analyser. The Makefile works around this by staging a copy under
    `.alloc-extract/` whose Cargo.toml is rewritten to `name = "alloc_models"`.
    Aeneas then writes its output into `lean/Aeneas/Alloc/` with everything in
    the `alloc_models` namespace; the helpers below put the namespace back to
    `alloc` (where downstream Aeneas-extracted code expects to find it).
    """
    text = text.replace("namespace alloc_models", "namespace CoreModels.alloc")
    text = text.replace("end alloc_models", "end CoreModels.alloc")
    text = text.replace("alloc_models", "alloc")
    return text


def rewrite_alloc_imports(text: str) -> str:
    """Adjust the imports / opens emitted by Aeneas for the staged alloc
    crate. The `alloc_models` rename has already happened by the time this
    runs, so the import paths still look like `import CoreModels.Alloc.<X>`
    (good — Aeneas emits those because of `-subdir CoreModels/Alloc`).
    """
    # Replace `import Aeneas` with the explicit pieces it needs.
    text = re.sub(
        r"^import Aeneas$",
        "import CoreModels.TypesPrologue\nimport CoreModels.Types\n"
        "import CoreModels.TypesExternal",
        text,
        flags=re.MULTILINE,
    )
    # Additional imports just for `Funs.lean`
    text = re.sub(
        r"^import CoreModels.Alloc.Types$",
        "import CoreModels.Alloc.Types\nimport CoreModels.FunsExternal\n"
        "import CoreModels.Funs",
        text,
        flags=re.MULTILINE,
    )
    # Drop imports of the alloc-side external files: their axioms now live
    # in the parent's `lean/Aeneas/FunsExternal.lean`, so the modules
    # `Aeneas.Alloc.{Funs,Types}External` don't exist anymore.
    text = re.sub(
        r"^import CoreModels\.Alloc\.(?:Funs|Types)External$",
        "-- (alloc-side externals live in parent Aeneas.FunsExternal)",
        text, flags=re.MULTILINE,
    )
    
    # Fix the `open`s: We want to open the Aeneas library definitions, except for
    # `core` and `alloc`.
    text = re.sub(
        r"^open Aeneas Aeneas\.Std Result ControlFlow Error$",
        "open Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen Result ControlFlow Error",
        text, flags=re.MULTILINE,
    )
    return text


def make_vec_pure_methods_pure(text: str) -> str:
    """Aeneas's standard library marks `Vec::new`, `Vec::with_capacity`,
    and `Vec::len` as `~can_fail:false ~lift:false`. Downstream
    Aeneas-extracted code therefore references them as bare expressions
    (e.g. `let i := v.len`), expecting them to return the value type
    directly, not `Result …`.

    Our extraction of the local `alloc/` crate emits these as monadic
    `Result T` defs. Identify each one by its doc-comment header and swap
    in a pure version. We also rename `vec.VecTGlobal.new`/`with_capacity`
    to `vec.Vec.new`/`with_capacity` so the names line up with Aeneas's
    builtin map (which always uses `vec.Vec.*`).

    The bodies use the fact that `rust_primitives.sequence.Seq T := Array T`
    in the parent's `TypesExternal.lean`, so we can build an empty `Seq`
    via `Array.empty` and read the length via the underlying list size.
    """
    return replace_blocks(text, [
        ("alloc::vec::{alloc::vec::Vec<T, alloc::alloc::Global>}::new",
         "def vec.Vec.new (T : Type) : vec.Vec T :=\n"
         "  (.new T, core.Phantom.mk)"),
        ("alloc::vec::{alloc::vec::Vec<T, alloc::alloc::Global>}::with_capacity",
         "def vec.Vec.with_capacity (T : Type) (_c : Std.Usize) : vec.Vec T :=\n"
         "  vec.Vec.new T"),
        ("alloc::vec::{alloc::vec::Vec<T, A>}::len",
         "def vec.Vec.len {T : Type} (self : vec.Vec T) : Std.Usize :=\n"
         "  let (s, _) := self\n"
         "  .mk (Std.Slice.len s)"),
    ])


def drop_vec_allocator_param(text: str) -> str:
    """Aeneas's standard library models `alloc::vec::Vec<T, A>` as a 1-arg
    `Vec α` (the allocator parameter is dropped via `keepParams`). Our
    extraction of the local `alloc/` crate sees the source as
    `Vec<T, A>(Seq<T>, PhantomData<A>)` and emits a 2-arg type. When a
    downstream test crate references std's `Vec<u32>`, charon translates
    it through Aeneas's builtin name map which produces 1-arg references —
    these don't match our 2-arg definition.

    Rewrite our extraction so `vec.Vec` (and the related drain types) take
    just `T`, with the phantom slot fixed to `core.Phantom Unit`.
    """
    # Type definitions: drop the second `(A : Type)` parameter and erase
    # `A` in the body. Each is identified by its doc-comment header so that a
    # change in line-wrapping or whitespace inside the body cannot silently
    # turn the rewrite into a no-op.
    text = replace_blocks(text, [
        ("alloc::vec::Vec",
         "def vec.Vec (T : Type) :=\n"
         "  rust_primitives.sequence.Seq T × core.Phantom Unit"),
        ("alloc::vec::drain::Drain",
         "def vec.drain.Drain (T : Type) :=\n"
         "  rust_primitives.sequence.Seq T × core.Phantom Unit"),
        ("alloc::vec::into_iter::IntoIter",
         "def vec.into_iter.IntoIter (T : Type) :=\n"
         "  rust_primitives.sequence.Seq T × core.Phantom Unit"),
    ])
    # Note: `collections.vec_deque.VecDeque` is intentionally left 2-arg
    # (Self + Allocator), matching std's `VecDeque<T, A>` shape, so that
    # downstream references like `alloc.collections.vec_deque.VecDeque T
    # Global` elaborate directly against our extracted type without any
    # rewrite. `Vec`/`Drain`/`IntoIter` still get collapsed to 1-arg
    # because Aeneas's builtin name map maps them that way.
    #
    # Function definitions: every `vec.Vec T A` reference becomes `vec.Vec T`.
    # Both the type parameter and the allocator can be a single identifier
    # (`T`, `A`, `Global`) or a dotted path (`Std.U32`, `alloc.alloc.Global`),
    # so we accept dots in both groups. The `\b` at the start matches the
    # boundary between `.` and the first letter, so the regex also fires on
    # downstream references like `alloc.vec.Vec Std.U32 alloc.alloc.Global`.
    for name in ("vec.Vec", "vec.drain.Drain",
                 "vec.into_iter.IntoIter"):
        # Both the type parameter and the allocator can appear either as a
        # simple/dotted identifier (`T`, `A`, `Global`, `Std.U32`,
        # `alloc.alloc.Global`) or as a parenthesized type expression
        # (e.g. `VecDeque (Seq U8) Global`). Accept both for group 1 and
        # for the allocator slot; `[^()]*?` keeps the non-nested match
        # local to a single balanced pair so we don't over-consume.
        arg = r"(?:\([^()]*\)|[A-Za-z_][\w.]*)"
        text = re.sub(
            rf"\b{re.escape(name)}\s+({arg})\s+{arg}",
            rf"{name} \1",
            text,
        )

    # Drop the now-unused `{A : Type}` binder.
    text = re.sub(
        r"(def vec\.(?:Vec|drain)[A-Za-z0-9._]+\s+[({]T : Type[)}])\s+[({]A : Type[)}]",
        r"\1",
        text,
    )

    return text


def rewrite_alloc_phantom_data(text: str) -> str:
    """Aeneas's alloc extraction declares `core::marker::PhantomData (T) := Unit`
    inside its own namespace and then references that path in struct field
    types. The constructor sites use `()`.

    Core's hand-written Types.lean already has a `core.marker.PhantomData`
    at the *root* path, but its body is `:= T`, which doesn't accept `()`.

    Rather than fight the conflict, we:

      - rewrite every `core.marker.PhantomData A` *type-level* reference in
        the alloc files to `core.Phantom A` (a *non-reducible* `structure`
        with a phantom type parameter — see `Aeneas/Primitives.lean`). The
        non-reducibility is important: a `def` would let Lean unfold the
        alias and lose `A` during unification, breaking the `{A : Type}`
        implicit at call sites like `alloc.vec.Vec.clear v`.

      - rewrite every `()` constructor in a phantom-field position to
        `core.Phantom.mk`. The constructor sites in the extracted alloc
        Funs.lean look like `(seq, ())` (or `(seq, pd)` when the variable
        was destructured); we leave the destructured form alone but
        rewrite the bare `()` form via a textual heuristic: `, ()` inside
        a tuple-construction expression on a line that builds a `vec.Vec`
        / `VecDeque` / `Drain` value.

      - erase the now-redundant `def core.Phantom (T) := Unit` block that
        Aeneas emitted in `Types.lean`.
    """
    # 1. Type-level: `core.marker.PhantomData` -> `core.Phantom`.
    text = re.sub(
        r"\bcore\.marker\.PhantomData\b",
        "core.Phantom",
        text,
    )
    # 2. Constructor-site: `, ())` (closing the outer pair) -> `, core.Phantom.mk)`.
    #    Aeneas's extraction always wraps the phantom in the second slot
    #    of a 2-tuple immediately followed by `)`.
    text = re.sub(r",\s*\(\)\)", ", core.Phantom.mk)", text)
    # 3. Erase the (now redundant) declaration block.
    return comment_out_blocks(
        text, ["core::marker::PhantomData"],
        trailer="replaced by core.Phantom (see rewrite_alloc_phantom_data)",
    )


def rename_clone_clone_inst(text: str) -> str:
    """Aeneas's standard library names `marker.Copy`'s clone-instance field
    `cloneInst`, but `core_models::marker::Copy` uses the macro-generated
    `cloneCloneInst`. We forward-declare `marker.Copy` in `TypesPrologue.lean`
    with the Aeneas-compatible name `cloneInst`, so we have to rewrite the
    field accessor in the generated code accordingly.

    There are three syntactic forms to rewrite:

      1. Field projection:        ‹e›.cloneCloneInst
      2. Record-literal label:    cloneCloneInst :=
      3. Local binders/uses introduced by Aeneas as the parameter name —
         these have the same identifier as the field. Since the binder name
         is independent of the field name, only the *label* in the record
         literal needs to change. We rename binders too for readability.
    """
    # Field label in record literals: `cloneCloneInst :=`
    text = re.sub(r"\bcloneCloneInst\s*:=", "cloneInst :=", text)
    # Field projection: `<expr>.cloneCloneInst`
    text = re.sub(r"\.cloneCloneInst\b", ".cloneInst", text)
    return text


def desugar_pure_num_bound_binds(text: str) -> str:
    """The generated `Funs.lean` uses monadic bind syntax to fetch numeric
    bounds:

        let i ← num.Isize.MIN
        let i ← num.U64.MAX

    because in the original Aeneas extraction those bounds are `Result <T>`
    (computed via `rust_primitives.arithmetic.<X>_{MIN,MAX}`). Our
    `Aeneas.Primitives` provides them as PURE values, so the call sites must
    use `:=` instead of `←`. Rewrite all such bind occurrences.
    """
    int_alt = "(?:U8|U16|U32|U64|U128|Usize|I8|I16|I32|I64|I128|Isize)"
    pat = re.compile(
        rf"(let\s+\w+)\s+←\s+(num\.{int_alt}\.(?:MIN|MAX))\b"
    )
    return pat.sub(r"\1 := \2", text)


def comment_out_num_bounds(text: str) -> str:
    """Aeneas extracts `core.num.<X>.MIN/MAX` as a mix of pure literals and
    monadic axioms (depending on whether the bound is computable). We
    forward-declare them all as PURE in `Aeneas.Primitives` so that earlier
    code in `Funs.lean` (which references them via `IScalar.cast`) can find
    them. The duplicates that follow in `Funs.lean` must be commented out.

    Each generated bound looks like:

        /-- [core_models::num::{core_models::num::<x>}::MIN]
            Source: ...
            Visibility: public -/
        @[global_simps, irreducible] def num.X.MIN : Std.X := ...

    Wrap the doc comment + attribute + def line in `/- ... -/` so the doc
    comment doesn't dangle.
    """
    types = ("u8", "u16", "u32", "u64", "u128", "usize",
             "i8", "i16", "i32", "i64", "i128", "isize")
    subs = [f"{{core_models::num::{t}}}::{b}"
            for t in types for b in ("MIN", "MAX")]
    return comment_out_blocks(text, subs, trailer="provided by CoreModels.FunsPrologue")


def add_funs_prologue_import(text: str) -> str:
    """Funs.lean needs CoreModels.FunsPrologue."""
    return text.replace(
        "import Aeneas\n",
        "import Aeneas\n"
        "import CoreModels.FunsPrologue\n",
    )

# Identifies the start of a top-level "block" (a doc comment, an attribute,
# or a bare def/structure/inductive/abbrev/instance line).
BLOCK_START_RE = re.compile(
    r"^(/--|@\[|def |structure |inductive |abbrev |instance |theorem |@\[reducible\])"
)
#  /-- [core_models::foo::Bar]:                (function definitions)
#  /-- [core_models::foo::Bar]                  (type / inductive definitions)
#
# The captured group must allow nested `[...]` because some name patterns
# include things like `<&'a ([T])>`. We use a non-greedy regex that ends at
# `]:` (function defs) or `]\n` / `]$` (type defs). Aeneas always closes the
# header `[...]` at the END of a line.
DOC_HEADER_RE = re.compile(r"^/--\s*\[(.*)\](?::.*)?\s*$")
# /-- Trait declaration: [core_models::clone::Clone]
# /-- Trait implementation: [core_models::...]
DOC_HEADER_TRAIT_RE = re.compile(
    r"^/--\s*Trait (?:declaration|implementation):\s*\[(.*)\](?::.*)?\s*$"
)


DEF_KEYWORDS = (
    "def ", "structure ", "inductive ", "abbrev ",
    "instance ", "theorem ", "noncomputable def ",
)


def _parse_doc_header(line: str) -> str | None:
    """Return the identifier inside a `/-- [path::to::name]` (or trait-decl /
    trait-impl) doc-comment header, or `None` if the line is not a header."""
    m = DOC_HEADER_RE.match(line)
    if m is None:
        m = DOC_HEADER_TRAIT_RE.match(line)
    return m.group(1) if m else None


def _find_block_end(lines: list[str], i: int, n: int) -> tuple[int, int]:
    """Given that `lines[i]` starts a `/--` doc-comment, locate the end of
    the logical block that follows.

    Returns `(end, j)` where:
      - `lines[i:end]` covers doc + `@[...]` attrs + one `DEF_KEYWORDS` line
        + body, with any trailing blank lines trimmed.
      - `j` is the cursor just past those trimmed blanks, so callers can
        re-emit `lines[end:j]` to preserve spacing.
    """
    # 1. Consume the doc-comment (until line ending with `-/`).
    j = i
    while j < n and not lines[j].rstrip().endswith("-/"):
        j += 1
    j += 1  # past the `-/`
    # 2. Consume any attributes (`@[...]`) and the def/structure/... keyword
    #    line — these belong to the same logical block.
    while j < n and lines[j].startswith("@["):
        j += 1
    if j < n and any(lines[j].startswith(k) for k in DEF_KEYWORDS):
        j += 1
    # 3. Consume the body: every line until the next top-level construct
    #    (`/--`, `@[`, a fresh def-keyword line, or a namespace `end ...`).
    while j < n:
        cur = lines[j]
        if cur.startswith("/--") or cur.startswith("@["):
            break
        if any(cur.startswith(k) for k in DEF_KEYWORDS):
            break
        if cur.startswith("end ") or cur.rstrip() == "end":
            break
        j += 1
    # Trim trailing blank lines from the block (they belong outside).
    end = j
    while end > i and lines[end - 1].strip() == "":
        end -= 1
    return end, j


def _ident_matches(ident: str, sub: str) -> bool:
    """Substring match modes used by both `comment_out_blocks` and
    `replace_blocks`:

      * `"foo::"`  — prefix match (entry ends with `::`)
      * exact equality
      * word-bounded suffix match (so `is_some` doesn't match `is_some_and`)
      * containment, when the entry contains `<` or `{` (used to drop
        everything matching a prefix anywhere in the path)
    """
    if sub.endswith("::"):
        return ident.startswith(sub)
    if ident == sub:
        return True
    if ident.endswith(sub):
        prev_char = ident[-len(sub) - 1]
        if not (prev_char.isalnum() or prev_char == "_"):
            return True
    if "<" in sub or "{" in sub:
        if sub in ident:
            return True
    return False


def transform_blocks(text: str, transform_fn) -> str:
    """Walk every top-level doc-headed block in `text`. For each block,
    `transform_fn(ident, block_lines)` is called with the bracketed identifier
    and the list of lines that make up the block. It must return either:

      * `None` to leave the block unchanged, or
      * a string to splice in place of the block. The string is split on
        `\\n` and emitted as line entries; trailing blank lines that followed
        the block in the original are preserved.

    Replacement strings should NOT include a trailing newline — line spacing
    is reconstructed by the final `"\\n".join(...)` plus the re-emitted
    trailing blanks.
    """
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if line.startswith("/--"):
            ident = _parse_doc_header(line)
            if ident is not None:
                end, j = _find_block_end(lines, i, n)
                replacement = transform_fn(ident, lines[i:end])
                if replacement is not None:
                    out.extend(replacement.split("\n"))
                    out.extend(lines[end:j])
                    i = j
                    continue
        out.append(line)
        i += 1
    return "\n".join(out)


def comment_out_blocks(
    text: str,
    name_substrings: list[str],
    *,
    trailer: str | None = None,
) -> str:
    """Find each top-level block whose doc-comment header contains one of the
    given substrings, and wrap that block in `/- -/`. If `trailer` is given,
    a `  -- <trailer>` suffix is appended after the closing `-/`.

    A block starts at a `/-- ... -/` doc comment (the start line) and runs
    until the next blank line followed by another block start, or to a clearly
    new block start (`/--`, `@[`, `def`, etc.).
    """
    suffix = "-/" if trailer is None else f"-/  -- {trailer}"

    def fn(ident: str, block_lines: list[str]) -> str | None:
        if any(_ident_matches(ident, s) for s in name_substrings):
            return "/-\n" + "\n".join(block_lines) + "\n" + suffix
        return None

    return transform_blocks(text, fn)


def replace_blocks(text: str, replacements: list[tuple[str, str]]) -> str:
    """Replace the def body of each top-level doc-headed block whose
    identifier contains a matching substring.

    `replacements` is a list of `(substring, replacement_text)` pairs;
    matching uses the same modes as `comment_out_blocks`. First match wins,
    so order entries from most-specific to least-specific if any could
    overlap. The original `/-- ... -/` doc-comment header is preserved;
    only the attributes / def / body that follow it are swapped for
    `replacement_text`.
    """
    def fn(ident: str, block_lines: list[str]) -> str | None:
        for sub, repl in replacements:
            if _ident_matches(ident, sub):
                # Preserve the doc-comment lines (up to and including the
                # one ending in `-/`); replace everything after.
                doc_end = 0
                while doc_end < len(block_lines) and \
                        not block_lines[doc_end].rstrip().endswith("-/"):
                    doc_end += 1
                doc_end += 1
                return "\n".join(block_lines[:doc_end]) + "\n" + repl
        return None

    return transform_blocks(text, fn)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    if not LEAN_DIR.exists():
        print(f"error: {LEAN_DIR} does not exist", file=sys.stderr)
        return 1
    CORE_DIR.mkdir(exist_ok=True)

    moved_any = False
    for filename in GENERATED_FILES:
        src = LEAN_DIR / filename
        dst = CORE_DIR / filename
        if not src.exists():
            print(f"warning: {src} not found, skipping", file=sys.stderr)
            continue
        shutil.move(str(src), str(dst))
        moved_any = True
        print(f"moved {src.name} -> Aeneas/{dst.name}")

    if not moved_any:
        print("nothing to patch (no freshly extracted files found)")

    # Apply transforms in dependency order: Types -> FunsExternal -> Funs
    types_path = CORE_DIR / "Types.lean"
    funs_path = CORE_DIR / "Funs.lean"
    funs_ext_path = CORE_DIR / "FunsExternal_Template.lean"
    types_ext_path = CORE_DIR / "TypesExternal_Template.lean"

    for path in [types_path, types_ext_path, funs_ext_path, funs_path]:
        if not path.exists():
            continue
        text = read(path)
        text = rewrite_imports_and_opens(text)
        text = rename_namespace(text)
        text = rename_clone_clone_inst(text)
        if path == funs_path:
            text = fix_fail_panic(text)
            text = add_funs_prologue_import(text)
            text = comment_out_num_bounds(text)
            text = desugar_pure_num_bound_binds(text)
        write(path, text)
        print(f"rewrote imports/opens/namespace in Aeneas/{path.name}")

    if types_path.exists():
        text = read(types_path)
        text = comment_out_blocks(text, TYPES_TO_REMOVE)
        write(types_path, text)
        print(f"commented out conflicting type defs in Aeneas/Types.lean")

    if funs_path.exists():
        text = read(funs_path)
        write(funs_path, text)
        print(f"commented out broken/duplicate function defs in Aeneas/Funs.lean")

    # ----- alloc/ patches ---------------------------------------------------
    patch_alloc()

    print("done.")
    return 0


def patch_alloc() -> None:
    """Process the Aeneas-extracted alloc files (under `lean/Aeneas/Alloc/`).

    Aeneas writes them with the staged crate name `alloc_models`. We rename
    everything back to `alloc`, fix imports/opens. The alloc subdirectory
    holds only the two files Aeneas can populate by itself (`Funs.lean`
    and `Types.lean`); the external axioms it would otherwise emit
    (under `*External_Template.lean`) live in the parent's
    `lean/Aeneas/FunsExternal.lean` instead, so we delete the templates
    after extraction.
    """
    if not ALLOC_DIR.exists():
        return

    funs        = ALLOC_DIR / "Funs.lean"
    types       = ALLOC_DIR / "Types.lean"
    funs_ext_t  = ALLOC_DIR / "FunsExternal_Template.lean"
    types_ext_t = ALLOC_DIR / "TypesExternal_Template.lean"

    # 1. Delete the external templates — their contents live in
    #    `lean/Aeneas/{Funs,Types}External.lean` (parent directory).
    for path in [funs_ext_t, types_ext_t]:
        if path.exists():
            path.unlink()
            print(f"removed Aeneas/Alloc/{path.name} (axioms live in parent FunsExternal.lean)")

    # 2. Apply common rewrites to the remaining files.
    for path in [types, funs]:
        if not path.exists():
            continue
        text = read(path)
        text = rename_alloc_models(text)
        text = rewrite_alloc_imports(text)
        text = fix_fail_panic(text)
        write(path, text)
        print(f"rewrote alloc_models -> alloc in Aeneas/Alloc/{path.name}")

    # 3. Replace `core.marker.PhantomData` with `core.Phantom` in alloc
    #    Types.lean AND alloc Funs.lean (the two files have to agree on the
    #    shape of `vec.Vec`). Then drop the allocator type parameter from
    #    `vec.Vec` and friends so they line up with Aeneas's standard 1-arg
    #    `Vec α` shape that downstream test crates expect when they use
    #    `std::vec::Vec<T>`.
    for path in [types, funs]:
        if not path.exists():
            continue
        text = read(path)
        text = rewrite_alloc_phantom_data(text)
        text = drop_vec_allocator_param(text)
        if path == funs:
            text = make_vec_pure_methods_pure(text)
        write(path, text)
    print("rewrote PhantomData and dropped allocator param in Aeneas/Alloc/{Types,Funs}.lean")


if __name__ == "__main__":
    sys.exit(main())
