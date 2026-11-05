/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign

/-! # `AffineNielsPoint::conditional_assign`

Sets `self` to `other` if `choice = 1` and leaves it unchanged otherwise, coordinate by
coordinate.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 323:4-327:5"

Port note (ref-impl-simulation, Aeneas d119a474): the proof closes the limb goals with
`simp only [*, apply_ite UScalar.val]` in place of `split_ifs <;> simp_all`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace SubtleConditionallySelectable

/-- Each limb of each coordinate is `other`'s if `choice = 1`, else `self`'s. -/
@[step]
theorem conditional_assign_spec
    (self other : backend.serial.curve_models.AffineNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result :
        backend.serial.curve_models.AffineNielsPoint) =>
      (∀ i < 5, result.y_plus_x[i]!.val =
        if choice.val = 1#u8 then other.y_plus_x[i]!.val else self.y_plus_x[i]!.val) ∧
      (∀ i < 5, result.y_minus_x[i]!.val =
        if choice.val = 1#u8 then other.y_minus_x[i]!.val else self.y_minus_x[i]!.val) ∧
      (∀ i < 5, result.xy2d[i]!.val =
        if choice.val = 1#u8 then other.xy2d[i]!.val else self.xy2d[i]!.val) ⦄ := by
  unfold conditional_assign
  step*
  refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp only [*, apply_ite UScalar.val]

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
