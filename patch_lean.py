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
  * Comments out some function-level items that we forward-declare in
    `FunsPrologue.lean`.
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

# ---------------------------------------------------------------------------
# Definitions to comment out, by their `[core_models::...]` doc-comment header.
# A definition is "everything from its doc-comment up to the line before the
# next doc-comment / `@[...]` attribute / blank-line+def".
# ---------------------------------------------------------------------------

# Definitions in Funs.lean that should be replaced by stub comments.
# Each entry is the substring of the `[core_models::...]` doc header
# that uniquely identifies the def.
FUNS_TO_REMOVE = [
    # iter::traits::iterator helpers (use generic field projection)
    "core_models::iter::traits::iterator::iter_fold",
    "core_models::iter::traits::iterator::iter_all",
    "core_models::iter::traits::iterator::iter_any",
    "core_models::iter::traits::iterator::iter_find_map",
    "core_models::iter::traits::iterator::iter_position",
    "core_models::iter::traits::iterator::iter_count",
    "core_models::iter::traits::iterator::iter_last",
    "core_models::iter::traits::iterator::iter_for_each",
    "core_models::iter::traits::iterator::iter_reduce",
    "core_models::iter::traits::iterator::iter_min",
    "core_models::iter::traits::iterator::iter_max",
    "core_models::iter::traits::iterator::iter_nth",
    # IteratorMethods.<x> blanket implementations
    "IteratorMethods<Clause0_Item> for I}::max",
    "IteratorMethods<Clause0_Item> for I}::min",
    "IteratorMethods<Clause0_Item> for I}::skip",
    "IteratorMethods<Clause0_Item> for I}::take",
    "IteratorMethods<Clause0_Item> for I}::map",
    "IteratorMethods<Clause0_Item> for I}::step_by",
    "IteratorMethods<Clause0_Item> for I}::enumerate",
    "IteratorMethods<Clause0_Item> for I}::fold",
    "IteratorMethods<Clause0_Item> for I}::all",
    "IteratorMethods<Clause0_Item> for I}::any",
    "IteratorMethods<Clause0_Item> for I}::count",
    "IteratorMethods<Clause0_Item> for I}::last",
    "IteratorMethods<Clause0_Item> for I}::nth",
    "IteratorMethods<Clause0_Item> for I}::for_each",
    "IteratorMethods<Clause0_Item> for I}::reduce",
    "IteratorMethods<Clause0_Item> for I}::find_map",
    "IteratorMethods<Clause0_Item> for I}::position",
    # The IteratorMethods blanket instance itself
    "core_models::iter::traits::iterator::IteratorMethods<Clause0_Item> for I}",
    # Adapter `*::new` constructors that the above depend on
    "core_models::iter::adapters::skip::{core_models::iter::adapters::skip::Skip<I>}::new",
    "core_models::iter::adapters::filter::{core_models::iter::adapters::filter::Filter<I, P>}::new",
    "core_models::iter::adapters::take::{core_models::iter::adapters::take::Take<I>}::new",
    "core_models::iter::adapters::map::{core_models::iter::adapters::map::Map<I, F>}::new",
    "core_models::iter::adapters::step_by::{core_models::iter::adapters::step_by::StepBy<I>}::new",
    "core_models::iter::adapters::enumerate::{core_models::iter::adapters::enumerate::Enumerate<I>}::new",
    # StepBy / Filter Iterator instances (depend on commented-out adapter ::new)
    # The ident captured by the regex stops at the first `]`, so we need the
    # `::next` form (which catches the loop body, the loop, and the wrapper).
    "core_models::iter::adapters::step_by::{core_models::iter::traits::iterator::Iterator<Clause0_Item> for core_models::iter::adapters::step_by::StepBy<I>}::next",
    "core_models::iter::adapters::step_by::{core_models::iter::traits::iterator::Iterator<Clause0_Item> for core_models::iter::adapters::step_by::StepBy<I>}",
    "core_models::iter::adapters::filter::{core_models::iter::traits::iterator::Iterator<Clause0_Item> for core_models::iter::adapters::filter::Filter<I, P>}",
    # iter::range::IteratorRange.next references core.iter.range.IteratorRange.next which is not provided
    "core_models::iter::range::iter_range_next",
    # Slice iterator implementations referencing missing helpers
    "core_models::slice::iter::{core_models::iter::traits::iterator::Iterator<&'a ([T])> for core_models::slice::iter::Chunks<'a, T>}::next",
    "core_models::slice::iter::{core_models::iter::traits::iterator::Iterator<&'a ([T])> for core_models::slice::iter::Chunks<'a, T>}",
    "core_models::slice::iter::{core_models::iter::traits::iterator::Iterator<&'a ([T])> for core_models::slice::iter::ChunksExact<'a, T>}::next",
    "core_models::slice::iter::{core_models::iter::traits::iterator::Iterator<&'a ([T])> for core_models::slice::iter::ChunksExact<'a, T>}",
    "core_models::slice::iter::{core_models::iter::traits::iterator::Iterator<&'a ([T])> for core_models::slice::iter::Windows<'a, T>}::next",
    "core_models::slice::iter::{core_models::iter::traits::iterator::Iterator<&'a ([T])> for core_models::slice::iter::Windows<'a, T>}",
    # All slice::Slice<T>::* methods. The implicit namespace `slice.Slice`
    # opened by `def slice.Slice.foo` makes bare `Slice T` resolve to
    # `slice.Slice T = T` (a no-op alias from Types.lean) instead of the
    # `core.Slice T` from Primitives, so the bodies don't elaborate.
    "core_models::slice::{core_models::slice::Slice<T>",
    # IntoIterator instances that depend on commented-out helpers.
    # The `IntoIterator` trait now carries three type parameters
    # (`Self`, `Item`, `IntoIter`), so the impl name patterns reflect
    # two generic args inside the angle brackets.
    "core_models::slice::{core_models::iter::traits::collect::IntoIterator<&'a ([T]), core_models::slice::iter::Iter<'a, T>> for &'b ([T])}",
    "core_models::slice::{core_models::iter::traits::collect::IntoIterator<&'a (T), core_models::slice::iter::Iter<'a, T>> for &'a ([T])}",
    "core_models::slice::{core_models::iter::traits::collect::IntoIterator<core_models::slice::iter::Iter<'a, T>> for &'a ([T])}",
    # fill_loop body referencing commented-out helpers
    "core_models::slice::{core_models::slice::Slice<T>}::fill",
    # All result.Result.* methods. The implicit `result.Result` namespace
    # opened by `def result.Result.foo` clashes with our monadic `Result`
    # type and `ok`/`err` constructors, so the bodies don't elaborate
    # correctly. Drop them all — downstream code that needs `result::Result`
    # operations should use the inductive type's constructors directly.
    "core_models::result::{core_models::result::Result<T, E>",
    "core_models::result::{core_models::result::Result<core_models::option::Option<T>, E>",
    "core_models::result::{core_models::result::Result<core_models::result::Result<T, E>, E>",
    # NOTE: pure-fn duplicates of `core::option::Option::{is_some, is_none,
    # unwrap_or, take}`, `core::mem::{swap, replace}`, and the
    # `core::num::*::{wrapping_*, saturating_*, rotate_*, overflowing_*}`
    # arithmetic helpers are now stripped at the LLBC level by charon's
    # `--exclude` flag (see CHARON_EXCLUDES in the Makefile). They no longer
    # need to be commented out here.
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
    `Result T` defs. Rewrite each one to a pure version. We also rename
    `vec.VecTGlobal.new`/`with_capacity` to `vec.Vec.new`/`with_capacity`
    so the names line up with Aeneas's builtin map (which always uses
    `vec.Vec.*`).

    The bodies use the fact that `rust_primitives.sequence.Seq T := Array T`
    in the parent's `TypesExternal.lean`, so we can build an empty `Seq`
    via `Array.empty` and read the length via the underlying list size. -/
    """
    # vec.VecTGlobal.new -> vec.Vec.new (pure)
    text = re.sub(
        r"def vec\.VecTGlobal\.new \(T : Type\) : Result \(vec\.Vec T\) := do\n"
        r"  let s ← rust_primitives\.sequence\.seq_empty T\n"
        r"  ok \(s, core\.Phantom\.mk\)",
        (
            "def vec.Vec.new (T : Type) : vec.Vec T :=\n"
            "  (.new T, core.Phantom.mk)"
        ),
        text,
    )
    # vec.VecTGlobal.with_capacity -> vec.Vec.with_capacity (pure)
    text = re.sub(
        r"def vec\.VecTGlobal\.with_capacity\n"
        r"  \(T : Type\) \(_c : Std\.Usize\) : Result \(vec\.Vec T\) := do\n"
        r"  vec\.VecTGlobal\.new T",
        (
            "def vec.Vec.with_capacity (T : Type) (_c : Std.Usize) : vec.Vec T :=\n"
            "  vec.Vec.new T"
        ),
        text,
    )
    # vec.Vec.len: drop the monadic wrapper.
    text = re.sub(
        r"def vec\.Vec\.len\n"
        r"  \{T : Type\} \(self : vec\.Vec T\) : Result Std\.Usize := do\n"
        r"  let \(s, _\) := self\n"
        r"  rust_primitives\.sequence\.seq_len s",
        (
            "def vec.Vec.len {T : Type} (self : vec.Vec T) : Std.Usize :=\n"
            "  let (s, _) := self\n"
            "  .mk (Std.Slice.len s)"
        ),
        text,
    )
    return text


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
    # Type definition: drop the second `(A : Type)` parameter and erase
    # `A` in the body.
    text = re.sub(
        r"def vec\.Vec \(T : Type\) \(A : Type\) :=\n"
        r"  rust_primitives\.sequence\.Seq T × core\.Phantom A",
        "def vec.Vec (T : Type) :=\n"
        "  rust_primitives.sequence.Seq T × core.Phantom Unit",
        text,
    )
    text = re.sub(
        r"def vec\.drain\.Drain \(T : Type\) \(A : Type\) :=\n"
        r"  rust_primitives\.sequence\.Seq T × core\.Phantom A",
        "def vec.drain.Drain (T : Type) :=\n"
        "  rust_primitives.sequence.Seq T × core.Phantom Unit",
        text,
    )
    text = re.sub(
        r"def vec\.into_iter\.IntoIter \(T : Type\) \(A : Type\) :=\n"
        r"  rust_primitives\.sequence\.Seq T × core\.Phantom A",
        "def vec.into_iter.IntoIter (T : Type) :=\n"
        "  rust_primitives.sequence.Seq T × core.Phantom Unit",
        text,
    )
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

    # Drop the now-unused `{A : Type}` binder. The Vec-allocator parameter
    # `A` is always introduced as an implicit `{A : Type}` somewhere in the
    # binder list — sometimes adjacent to `{T : Type}` (e.g. impl methods
    # `{T : Type} {A : Type}`), sometimes interleaved with extra implicits
    # like `{T : Type} {I : Type} {A : Type} {Clause0_Output : Type}` for
    # the generic `Vec::index<I: SliceIndex<[T]>>` impl. Just remove every
    # `{A : Type}` binder unconditionally — `A` is exclusively the allocator
    # name in our extraction, never a user-chosen identifier.
    text = re.sub(r"\s*\{A : Type\}", "", text)

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
    pat = re.compile(
        r"^(/-- \[core::marker::PhantomData\]\n"
        r"(?:[^\n]*\n)*?"
        r"\ *Visibility:\ public\ -/\n)"
        r"(@\[[^\]]*\]\n)?"
        r"(def\s+core\.Phantom[^\n]*\n)",
        re.MULTILINE,
    )
    return pat.sub(
        lambda m: "/-\n" + m.group(0) + "-/  -- replaced by core.Phantom (see rewrite_alloc_phantom_data)\n",
        text,
    )


def rename_clone_clone_inst(text: str) -> str:
    """Aeneas's standard library names `marker.Copy`'s clone-instance field
    `cloneInst`, but `core_models::marker::Copy` uses the macro-generated
    `cloneCloneInst`. We forward-declare `marker.Copy` in `Primitives.lean`
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

    or with the attribute on its own line and the def on the next. We wrap
    the doc comment + (optional) attribute + def line in a `/- ... -/`
    block comment so the doc comment doesn't dangle.
    """
    int_alt = "(?:U8|U16|U32|U64|U128|Usize|I8|I16|I32|I64|I128|Isize)"
    # The full block: doc comment + optional attribute(s) + def line.
    # The `[^\]]*` inside the doc comment is generous (no nested `]`).
    pat = re.compile(
        rf"""
        ^(/--\ \[core_models::num::\{{core_models::num::[a-z0-9]+\}}::(?:MIN|MAX)\]\n
        (?:[^\n]*\n)*?           # doc body lines
        \ *Visibility:\ public\ -/\n)
        ((?:@\[[^\]]*\]\s*\n?)*) # zero or more attributes (each may end the line or continue)
        (def\s+num\.{int_alt}\.(?:MIN|MAX)[^\n]*\n)
        """,
        re.MULTILINE | re.VERBOSE,
    )

    def repl(m: re.Match) -> str:
        body = m.group(0)
        return "/-\n" + body + "-/  -- provided by Aeneas.Primitives\n"

    return pat.sub(repl, text)


def fix_flatten_signature(text: str) -> str:
    """Aeneas generates `Flatten IteratorInst IteratorInst` which doesn't
    typecheck because the two arguments need different iterator instances."""
    pattern = (
        r"  flatten : forall \{Clause0_Item : Type\} \(IteratorInst :\n"
        r"    iter\.traits\.iterator\.Iterator Self_Clause0_Item Clause0_Item\), Self →\n"
        r"    Result \(iter\.adapters\.flatten\.Flatten IteratorInst IteratorInst\)"
    )
    replacement = (
        "  flatten : forall {Clause0_Item : Type} (IteratorInst :\n"
        "    iter.traits.iterator.Iterator Self_Clause0_Item Clause0_Item)\n"
        "    (SelfIteratorInst : iter.traits.iterator.Iterator Self Self_Clause0_Item),\n"
        "    Self →\n"
        "    Result (iter.adapters.flatten.Flatten SelfIteratorInst IteratorInst)"
    )
    return re.sub(pattern, replacement, text)


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


def comment_out_blocks(text: str, name_substrings: list[str]) -> str:
    """Find each top-level block whose doc-comment header contains one of the
    given substrings, and wrap that block in `/- -/`.

    A block starts at a `/-- ... -/` doc comment (the start line) and runs
    until the next blank line followed by another block start, or to a clearly
    new block start (`/--`, `@[`, `def`, etc.).
    """
    lines = text.split("\n")
    out: list[str] = []
    i = 0
    n = len(lines)

    def block_matches(doc_line: str) -> bool:
        m = DOC_HEADER_RE.match(doc_line)
        ident = m.group(1) if m else None
        if ident is None:
            m = DOC_HEADER_TRAIT_RE.match(doc_line)
            ident = m.group(1) if m else None
        if ident is None:
            return False
        for sub in name_substrings:
            # Three matching modes:
            #   "foo::"   prefix match (the entry ends with `::`)
            #   exact equality
            #   word-bounded suffix match (avoid `is_some` matching `is_some_and`)
            if sub.endswith("::"):
                if ident.startswith(sub):
                    return True
                continue
            if ident == sub:
                return True
            if ident.endswith(sub):
                prev_char = ident[-len(sub) - 1]
                if not (prev_char.isalnum() or prev_char == "_"):
                    return True
            # Substring containment with start anchored to a `::` boundary —
            # used for "drop everything matching this prefix anywhere".
            if "<" in sub or "{" in sub:
                if sub in ident:
                    return True
        return False

    DEF_KEYWORDS = (
        "def ", "structure ", "inductive ", "abbrev ",
        "instance ", "theorem ", "noncomputable def ",
    )

    while i < n:
        line = lines[i]
        # Detect a doc-comment block start
        if line.startswith("/--") and block_matches(line):
            # 1. Consume the doc-comment (until line ending with `-/`).
            j = i
            while j < n and not lines[j].rstrip().endswith("-/"):
                j += 1
            j += 1  # past the `-/`
            # 2. Consume any attributes (`@[...]`) and the def/structure/...
            #    keyword line — these belong to the same logical block.
            while j < n and lines[j].startswith("@["):
                j += 1
            # The definition keyword line itself.
            if j < n and any(lines[j].startswith(k) for k in DEF_KEYWORDS):
                j += 1
            # 3. Consume the body: all subsequent lines that are indented
            #    or that continue the current declaration. Stop at the next
            #    top-level construct (blank line followed by `/--`/`@[`/def,
            #    or a fresh `/--`/`@[` with no leading blank).
            while j < n:
                cur = lines[j]
                if cur.startswith("/--") or cur.startswith("@["):
                    break
                if any(cur.startswith(k) for k in DEF_KEYWORDS):
                    # New top-level def starts here.
                    break
                j += 1
            # Trim trailing blank lines from the block (they belong outside).
            end = j
            while end > i and lines[end - 1].strip() == "":
                end -= 1
            out.append("/-")
            out.extend(lines[i:end])
            out.append("-/")
            # Re-emit the trimmed blank lines so spacing is preserved.
            out.extend(lines[end:j])
            i = j
            continue
        out.append(line)
        i += 1
    return "\n".join(out)


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
        if path == types_path:
            text = fix_flatten_signature(text)
        write(path, text)
        print(f"rewrote imports/opens/namespace in Aeneas/{path.name}")

    if types_path.exists():
        text = read(types_path)
        text = comment_out_blocks(text, TYPES_TO_REMOVE)
        write(types_path, text)
        print(f"commented out conflicting type defs in Aeneas/Types.lean")

    if funs_path.exists():
        text = read(funs_path)
        text = comment_out_blocks(text, FUNS_TO_REMOVE)
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
