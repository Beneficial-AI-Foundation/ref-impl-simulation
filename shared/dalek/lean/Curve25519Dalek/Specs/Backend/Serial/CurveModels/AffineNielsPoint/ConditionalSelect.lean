/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect

/-! # `AffineNielsPoint::conditional_select`

Returns `b` if `choice = 1` and `a` otherwise. It applies `FieldElement51::conditional_select`
to each coordinate.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"

Port note (ref-impl-simulation, Aeneas d119a474): the proof closes the limb goals with
`simp only [*, apply_ite UScalar.val]` in place of `split_ifs <;> simp_all`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace SubtleConditionallySelectable

/-- Each limb of each coordinate is `b`'s if `choice = 1`, else `a`'s. -/
@[step]
theorem conditional_select_spec
    (a b : backend.serial.curve_models.AffineNielsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : backend.serial.curve_models.AffineNielsPoint) =>
      (∀ i < 5, result.y_plus_x[i]!.val =
        if choice.val = 1#u8 then b.y_plus_x[i]!.val else a.y_plus_x[i]!.val) ∧
      (∀ i < 5, result.y_minus_x[i]!.val =
        if choice.val = 1#u8 then b.y_minus_x[i]!.val else a.y_minus_x[i]!.val) ∧
      (∀ i < 5, result.xy2d[i]!.val =
        if choice.val = 1#u8 then b.xy2d[i]!.val else a.xy2d[i]!.val) ⦄ := by
  unfold conditional_select
  step*
  refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp only [*, apply_ite UScalar.val]

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
