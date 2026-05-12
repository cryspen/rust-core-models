/-
  Triple-style specifications (tagged `@[spec]`) for total Rust primitives
  that recur in cross-spec proofs but currently lack `@[spec]` lemmas in
  Aeneas std.

  The total bitwise primitives (`^^^` / `&&&` / `~~~`) are handled by the
  Aeneas `lift` wrapper — its `@[spec]` lemma lives in
  `Hax.MissingAeneas` (`attribute [spec] Function.uncurry lift`).

  This file adds spec lemmas for the rotate primitives, since they are
  pure and total but currently extract to a `Result`-monadic wrapper
  without a registered triple.
-/
import CoreModels.Funs
import CoreModels.FunsExternal

namespace core_models

open Aeneas Aeneas.Std Std.Do

set_option linter.unusedVariables false
set_option mvcgen.warning false

@[spec]
theorem num.U32.rotate_left_spec (x : Std.U32) (n : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ core_models.num.U32.rotate_left x n
    ⦃ ⇓ r => ⌜ r.bv = x.bv.rotateLeft n.val ⌝ ⦄ := by
  show ⦃ _ ⦄ rust_primitives.arithmetic.rotate_left_u32 x n ⦃ _ ⦄
  unfold rust_primitives.arithmetic.rotate_left_u32
  mvcgen [UScalar.rotate_left]

@[spec]
theorem num.U64.rotate_left_spec (x : Std.U64) (n : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ core_models.num.U64.rotate_left x n
    ⦃ ⇓ r => ⌜ r.bv = x.bv.rotateLeft n.val ⌝ ⦄ := by
  show ⦃ _ ⦄ rust_primitives.arithmetic.rotate_left_u64 x n ⦃ _ ⦄
  unfold rust_primitives.arithmetic.rotate_left_u64
  mvcgen [UScalar.rotate_left]

end core_models
