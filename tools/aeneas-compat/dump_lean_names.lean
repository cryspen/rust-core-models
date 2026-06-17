-- Dumps every constant name in the `CoreModels.core` / `CoreModels.alloc`
-- namespaces, one per line, for the forward-naming compat prototype.
-- Run from the `lean/` project:  lake env lean ../tools/aeneas-compat/dump_lean_names.lean
import CoreModels
open Lean
#eval show MetaM Unit from do
  let env ← getEnv
  let mut names : Array String := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "CoreModels.core." || s.startsWith "CoreModels.alloc." then
      names := names.push s
  for s in names.qsort (· < ·) do
    IO.println s
