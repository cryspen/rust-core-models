-- Resolver half of the `lean_extract_compat.py` tool.
--
-- Reads a newline-separated list of `core.*` / `alloc.*` candidate names from
-- the file named in the `CANDS` environment variable, and prints (one per line)
-- those that do NOT resolve against the `CoreModels` library — i.e. the genuine
-- gaps. Resolution uses the elaborator, so it accepts not just bare constants
-- but also dot-notation projections on instances (e.g. an instance term's
-- `.partial_cmp`), which a flat name lookup would wrongly flag as missing.
--
-- Run from the `lean/` project:
--   CANDS=/path/to/candidates.txt lake env lean ../tools/aeneas-compat/check_lean_missing.lean
import CoreModels
open Lean Meta Elab Term
open CoreModels

#eval show MetaM Unit from do
  let some path ← IO.getEnv "CANDS" | throwError "set the CANDS env var to the candidate-list file"
  let txt ← IO.FS.readFile path
  let env ← getEnv
  for line in txt.splitOn "\n" do
    let s := line.trimAscii
    if s.isEmpty then continue
    let n := s.toName
    -- Fast path: a real constant (defs, instances, auto-generated structure
    -- projections like `core.cmp.PartialEq.eq` are all constants). Short-circuit
    -- so that a constant which merely needs implicit/typeclass args can never be
    -- spuriously reported as missing by the elaboration fall-back below.
    let ok ← if env.contains n then pure true else
      (do
        let stx ← `($(mkIdent n))
        -- `withoutErrToSorry` makes an unknown identifier *throw* rather than be
        -- silently replaced by `sorry`; that's what lets us catch it here. This
        -- branch is what accepts dot-notation projections on instance terms.
        try
          let _ ← TermElabM.run' (withoutErrToSorry (elabTerm stx none))
          pure true
        catch _ => pure false)
    if !ok then IO.println s
