/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # `FieldElement51::from_limbs`

Builds a `FieldElement51` from five `u64` limbs. `FieldElement51` is `Array U64 5#usize`, so
the function returns its input.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- The result is `a`, so `Field51_as_Nat r = Field51_as_Nat a`. -/
@[step]
theorem from_limbs_spec (a : Array U64 5#usize) :
    from_limbs a ⦃ (r : FieldElement51) =>
      r = a ∧ Field51_as_Nat r = Field51_as_Nat a ⦄ := by
  simp [from_limbs]

end curve25519_dalek.backend.serial.u64.field.FieldElement51
