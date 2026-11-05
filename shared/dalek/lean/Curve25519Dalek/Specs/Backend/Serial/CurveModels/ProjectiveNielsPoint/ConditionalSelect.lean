/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect

/-! # `ProjectiveNielsPoint::conditional_select`

Returns `b` if `choice = 1` and `a` otherwise. It applies `FieldElement51::conditional_select`
to each coordinate.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 297:4-304:5"

Port note (ref-impl-simulation, Aeneas d119a474): the proof closes the limb goals with
`simp only [*, apply_ite UScalar.val]` in place of `split_ifs <;> simp_all`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
namespace curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts
namespace SubtleConditionallySelectable

/-- Each limb of each coordinate is `b`'s if `choice = 1`, else `a`'s. -/
@[step]
theorem conditional_select_spec
    (a b : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : ProjectiveNielsPoint) =>
      (∀ i < 5, result.Y_plus_X[i]!.val =
        if choice.val = 1#u8 then b.Y_plus_X[i]!.val else a.Y_plus_X[i]!.val) ∧
      (∀ i < 5, result.Y_minus_X[i]!.val =
        if choice.val = 1#u8 then b.Y_minus_X[i]!.val else a.Y_minus_X[i]!.val) ∧
      (∀ i < 5, result.Z[i]!.val =
        if choice.val = 1#u8 then b.Z[i]!.val else a.Z[i]!.val) ∧
      (∀ i < 5, result.T2d[i]!.val =
        if choice.val = 1#u8 then b.T2d[i]!.val else a.T2d[i]!.val) ⦄ := by
  unfold conditional_select
  step*
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i hi <;> simp only [*, apply_ite UScalar.val]

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts
