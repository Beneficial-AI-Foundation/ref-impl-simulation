/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # `constants::EDWARDS_D2`

The constant `2d mod p`, where `d` is the Edwards curve parameter and `p = 2^255 - 19`.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- `EDWARDS_D2` is `2d` mod `p`, with limbs `< 2^52`. -/
@[step]
theorem EDWARDS_D2_spec :
    EDWARDS_D2 ⦃ (result : field.FieldElement51) =>
      Field51_as_Nat result = (2 * d) % p ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  unfold EDWARDS_D2 field.FieldElement51.from_limbs
  simp only [spec_ok]
  decide

end curve25519_dalek.backend.serial.u64.constants
