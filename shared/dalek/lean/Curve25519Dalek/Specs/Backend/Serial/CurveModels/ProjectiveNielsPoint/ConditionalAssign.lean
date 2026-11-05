/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign

/-! # `ProjectiveNielsPoint::conditional_assign`

Sets `self` to `other` if `choice = 1` and leaves it unchanged otherwise, coordinate by
coordinate.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 306:4-311:5"

Port note (ref-impl-simulation, Aeneas d119a474): the limb goals close with
`simp only [*, apply_ite UScalar.val]` in place of `split_ifs <;> simp_all`. The two cases of
`choice` in `conditional_assign_point` use one new lemma, `eq_of_limb_vals`, and
`toPoint` maps to `DalekSim.Edwards.Point dEd`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
namespace curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts
namespace SubtleConditionallySelectable

/-- Each limb of each coordinate is `other`'s if `choice = 1`, else `self`'s. -/
@[step]
theorem conditional_assign_spec
    (self other : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result : ProjectiveNielsPoint) =>
      (∀ i < 5, result.Y_plus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_plus_X[i]!.val else self.Y_plus_X[i]!.val) ∧
      (∀ i < 5, result.Y_minus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_minus_X[i]!.val else self.Y_minus_X[i]!.val) ∧
      (∀ i < 5, result.Z[i]!.val =
        if choice.val = 1#u8 then other.Z[i]!.val else self.Z[i]!.val) ∧
      (∀ i < 5, result.T2d[i]!.val =
        if choice.val = 1#u8 then other.T2d[i]!.val else self.T2d[i]!.val) ⦄ := by
  unfold conditional_assign
  step*
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i hi <;> simp only [*, apply_ite UScalar.val]

/-- Two `ProjectiveNielsPoint`s with equal limb values are equal. -/
private theorem eq_of_limb_vals {r s : ProjectiveNielsPoint}
    (h1 : ∀ i < 5, r.Y_plus_X[i]!.val = s.Y_plus_X[i]!.val)
    (h2 : ∀ i < 5, r.Y_minus_X[i]!.val = s.Y_minus_X[i]!.val)
    (h3 : ∀ i < 5, r.Z[i]!.val = s.Z[i]!.val)
    (h4 : ∀ i < 5, r.T2d[i]!.val = s.T2d[i]!.val) : r = s := by
  have e1 := fe_eq_of_limbs fun i hi => UScalar.eq_of_val_eq (h1 i hi)
  have e2 := fe_eq_of_limbs fun i hi => UScalar.eq_of_val_eq (h2 i hi)
  have e3 := fe_eq_of_limbs fun i hi => UScalar.eq_of_val_eq (h3 i hi)
  have e4 := fe_eq_of_limbs fun i hi => UScalar.eq_of_val_eq (h4 i hi)
  cases r; cases s; simp only at e1 e2 e3 e4; subst e1 e2 e3 e4; rfl

/-- For valid `self` and `other`, `conditional_assign self other choice` is valid and its
`toPoint` is `other.toPoint` if `choice = 1`, else `self.toPoint`. -/
@[step]
theorem conditional_assign_point
    (self other : ProjectiveNielsPoint)
    (h_self : self.IsValid) (h_other : other.IsValid)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result : ProjectiveNielsPoint) =>
      result.IsValid ∧
      result.toPoint = (if choice.val = 1#u8 then other.toPoint else self.toPoint) ⦄ := by
  let* ⟨ r, r_post1, r_post2, r_post3, r_post4 ⟩ ← conditional_assign_spec
  by_cases hc : choice.val = 1#u8
  · simp only [hc, if_true] at r_post1 r_post2 r_post3 r_post4 ⊢
    rw [eq_of_limb_vals r_post1 r_post2 r_post3 r_post4]
    exact ⟨h_other, rfl⟩
  · simp only [hc, if_false] at r_post1 r_post2 r_post3 r_post4 ⊢
    rw [eq_of_limb_vals r_post1 r_post2 r_post3 r_post4]
    exact ⟨h_self, rfl⟩

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts
