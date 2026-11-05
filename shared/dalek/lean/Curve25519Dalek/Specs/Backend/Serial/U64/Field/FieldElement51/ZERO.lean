/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-! # `FieldElement51::ZERO`

The constant `0`, stored as the limbs `[0, 0, 0, 0, 0]`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- `ZERO` is `0`, with limbs `< 2^51`. -/
@[step]
theorem ZERO_spec :
    ZERO ⦃ (result : FieldElement51) =>
      Field51_as_Nat result = 0 ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold ZERO
  step*
  simp only [*]
  decide

end curve25519_dalek.backend.serial.u64.field.FieldElement51
