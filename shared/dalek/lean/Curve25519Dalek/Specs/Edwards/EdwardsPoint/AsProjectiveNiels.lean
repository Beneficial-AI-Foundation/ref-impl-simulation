/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EdwardsD2
import Curve25519Dalek.Auxiliary

/-!
# `EdwardsPoint::as_projective_niels`

`as_projective_niels` maps extended coordinates `(X, Y, Z, T)` to projective Niels
coordinates `(Y + X, Y - X, Z, T · 2d)` modulo `p`.

Source: "curve25519-dalek/src/edwards.rs"

Port note (ref-impl-simulation, Aeneas d119a474): `step*` on this pin names the two
postconditions of a call `x_post` and `x_post1` instead of `x_post1` and `x_post2`. The proof
uses the new names. `toPoint` maps to `DalekSim.Edwards.Point dEd`. The rest is unchanged.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
  curve25519_dalek.backend.serial.u64.constants
  curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint
  curve25519_dalek.montgomery
namespace curve25519_dalek.edwards.EdwardsPoint

/-- For a valid `self`, `as_projective_niels self` is valid and represents the same point. Its
coordinates satisfy `Y_plus_X ≡ Y + X`, `Y_minus_X + X ≡ Y`, `Z ≡ Z` and `T2d ≡ T · (2 · d)`
mod `p`. -/
@[step]
theorem as_projective_niels_spec
    (self : EdwardsPoint)
    (hself : self.IsValid) :
    as_projective_niels self ⦃ (pn : backend.serial.curve_models.ProjectiveNielsPoint) =>
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let T := Field51_as_Nat self.T
      let A := Field51_as_Nat pn.Y_plus_X
      let B := Field51_as_Nat pn.Y_minus_X
      let Z' := Field51_as_Nat pn.Z
      let C := Field51_as_Nat pn.T2d
      A % p = (Y + X) % p ∧
      (B + X) % p = Y % p ∧
      Z' % p = Z % p ∧
      C % p = (T * (2 * d)) % p ∧
      (∀ i < 5, (pn.Y_plus_X[i]!).val < 2 ^ 54 ∧
      ∀ i < 5, (pn.Y_minus_X[i]!).val < 2 ^ 52 ∧
      ∀ i < 5, (pn.Z[i]!).val < 2 ^ 53 ∧
      ∀ i < 5, (pn.T2d[i]!).val < 2 ^ 52) ∧
      pn.IsValid ∧
      self.toPoint = pn.toPoint ⦄ := by
  unfold as_projective_niels
  step*
  · exact hself.Y_bounds
  · have := hself.X_bounds
    exact this
  · have := hself.T_bounds
    -- mathlib v4.30 drift: grind needs Array.getElem!_Nat_eq hint
    grind [Array.getElem!_Nat_eq]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · congr 1; exact pointwise_add_Field51_as_Nat self.Y self.X fe fe_post
    · assumption
    · simp_all [Nat.ModEq]
    · constructor
      · have := hself.Z_bounds
        simp_all
      · have := pointwise_add_Field51_as_Nat self.Y self.X fe fe_post
        rw [← Nat.ModEq, Edwards.lift_mod_eq_iff] at fe1_post1
        have : (Field51_as_Nat fe1) =
            (Field51_as_Nat self.Y) - ((Field51_as_Nat self.X) : Edwards.CurveField) := by grind
        rw [Edwards.lift_mod_eq_iff] at fe3_post
        have : ({ Y_plus_X := fe, Y_minus_X := fe1, Z := self.Z, T2d := fe3 } :
            backend.serial.curve_models.ProjectiveNielsPoint).IsValid := by
          refine
            { Z_ne_zero := ?_, T2d_relation := ?_, on_curve := ?_,
              Y_plus_X_bounds := ?_, Y_minus_X_bounds := ?_,
              Z_bounds := ?_, T2d_bounds := ?_ }
          · have := hself.Z_ne_zero
            simp_all
          · unfold toField
            simp_all only
            have := hself.T_relation
            unfold toField at this
            ring_nf
            have : Edwards.Ed25519.d = d := rfl
            grind
          · unfold toField
            simp_all only
            have := hself.on_curve
            simp only at this
            unfold toField at this
            grind
          · simp_all  -- Y_plus_X_bounds: < 2^54
          · -- Y_minus_X_bounds: goal < 2^54, fact fe1_post : < 2^52
            -- mathlib v4.30 drift: agrind no longer closes; use grind with hint
            intro i hi; have := fe1_post i hi; grind [Array.getElem!_Nat_eq]
          · have := hself.Z_bounds
            simp_all
          · -- T2d_bounds: < 2^52
            -- mathlib v4.30 drift: agrind no longer closes; use grind with hint
            intro i hi; have := fe3_post1 i hi; grind [Array.getElem!_Nat_eq]
        simp only [this, true_and]
        unfold toPoint backend.serial.curve_models.ProjectiveNielsPoint.toPoint
        simp only [hself, ↓reduceDIte, this]
        unfold toPoint'
          backend.serial.curve_models.ProjectiveNielsPoint.toPoint' toField
        simp_all only
        have := hself.Z_ne_zero
        unfold toField at this
        field_simp
        -- mathlib v4.30 drift: grind can't close; use congr+push_cast+field_simp+ring
        congr 1 <;> push_cast <;> field_simp <;> ring

end curve25519_dalek.edwards.EdwardsPoint
