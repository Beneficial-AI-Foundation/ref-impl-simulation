/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import DalekSim.Basic
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended

/-!
# `EdwardsPoint::mul_by_pow_2`

`mul_by_pow_2 self k` doubles `self` `k` times and so computes `2^k • self`. It asserts `k > 0`.

Source: "curve25519-dalek/src/edwards.rs"

Port note (ref-impl-simulation, Aeneas d119a474): points are in
`DalekSim.Edwards.Point dEd`. The binds are reduced with `Std.bind_ok` in place of
`bind_tc_ok`, and `spec_imp_exists` is replaced by `DalekSim.exists_ok_of_spec`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
  curve25519_dalek.backend.serial.curve_models.ProjectivePoint
  curve25519_dalek.backend.serial.u64.field
open DalekSim (dEd)
open DalekSim.Edwards (Point)
namespace curve25519_dalek.edwards.EdwardsPoint

/-- Loop of `mul_by_pow_2`: for `k > 0` and `i ≤ k - 1`, if `s` represents `2^i • P₀`, the
result represents `2^(k-1) • P₀`. The invariant bounds the limbs of `X` and `Y` by `2^53`, which
`double` needs. The input from `as_projective` meets it, and each iteration gives `2^52`. -/
@[step]
theorem mul_by_pow_2_loop_spec
    (k : U32) (s : ProjectivePoint) (i : U32)
    (hk : k.val > 0) (hi : i.val ≤ k.val - 1)
    (hs_on : s.OnCurve)
    (hs_X : ∀ j < 5, s.X[j]!.val < 2 ^ 53)
    (hs_Y : ∀ j < 5, s.Y[j]!.val < 2 ^ 53)
    (hs_Z : s.Z.IsValid)
    (P₀ : Point dEd)
    (hs_point : s.toPoint' hs_on = 2 ^ i.val • P₀) :
    mul_by_pow_2_loop k s i ⦃ (result : ProjectivePoint) =>
      ∃ h_on : result.OnCurve,
      (∀ j < 5, result.X[j]!.val < 2 ^ 53) ∧
      (∀ j < 5, result.Y[j]!.val < 2 ^ 53) ∧
      result.Z.IsValid ∧
      result.toPoint' h_on = 2 ^ (k.val - 1) • P₀ ⦄ := by
  induction h_rem : (k.val - 1 - i.val) generalizing i s with
  | zero =>
    -- i.val = k.val - 1, loop returns ok s
    have hi_eq : i.val = k.val - 1 := by omega
    unfold mul_by_pow_2_loop
    step as ⟨i1, hi1_post1, hi1_post2⟩
    have hilt : ¬ (i < i1) := by scalar_tac
    simp only [hilt, ↓reduceIte, spec_ok]
    refine ⟨hs_on, hs_X, hs_Y, hs_Z, ?_⟩
    rw [← hi_eq]; exact hs_point
  | succ n ih =>
    -- i.val < k.val - 1, body executes then recurses
    have hlt : i.val < k.val - 1 := by omega
    unfold mul_by_pow_2_loop
    step as ⟨i1, hi1_post1, hi1_post2⟩
    have hiltu : i < i1 := by scalar_tac
    simp only [hiltu, ↓reduceIte]
    -- double s → r with r.IsValid, r.toPoint = s.toPoint' hs_on + s.toPoint' hs_on
    obtain ⟨r, hr_run, hr_valid, hr_toPoint⟩ :=
      double_spec_core s hs_on hs_X hs_Y hs_Z
    simp only [hr_run, Std.bind_ok]
    -- CompletedPoint.as_projective r → proj with proj.IsValid, proj.toPoint = r.toPoint
    obtain ⟨proj, hproj_run, hproj_valid, hproj_toPoint⟩ :=
      DalekSim.exists_ok_of_spec (CompletedPoint.as_projective_spec r hr_valid)
    simp only [Std.bind_ok, hproj_run, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      exists_and_left]
    -- Increment counter
    step as ⟨i2, hi2_post1⟩
    -- Build IH preconditions for (proj, i2)
    have h_proj_on : proj.OnCurve := hproj_valid.toOnCurve
    have h_proj_X : ∀ j < 5, proj.X[j]!.val < 2 ^ 53 :=
      fun j hj => Nat.lt_of_lt_of_le (hproj_valid.X_bounds j hj) (by norm_num)
    have h_proj_Y : ∀ j < 5, proj.Y[j]!.val < 2 ^ 53 :=
      fun j hj => Nat.lt_of_lt_of_le (hproj_valid.Y_bounds j hj) (by norm_num)
    have h_proj_Z : proj.Z.IsValid :=
      FieldElement51.IsValid_of_lt_pow hproj_valid.Z_bounds (by decide)
    -- Point chain: s.toPoint' = 2^i • P₀ → r.toPoint = 2 • s.toPoint' = 2^(i+1) • P₀
    -- → proj.toPoint = r.toPoint → proj.toPoint' = proj.toPoint (IsValid)
    have h_proj_point : proj.toPoint' h_proj_on = 2 ^ i2.val • P₀ := by
      have heq_topoint : proj.toPoint' h_proj_on = proj.toPoint := by
        unfold ProjectivePoint.toPoint; rw [dif_pos hproj_valid]
      have hi2_val : i2.val = i.val + 1 := by scalar_tac
      rw [heq_topoint, hproj_toPoint, hr_toPoint, hs_point, hi2_val,
          ← two_nsmul, ← mul_smul]
      congr 1; ring
    -- Apply IH at (proj, i2) with remaining counter n
    have h_i2_le : i2.val ≤ k.val - 1 := by scalar_tac
    have h_new_rem : k.val - 1 - i2.val = n := by scalar_tac
    let* ⟨ result, h_on, hX, hY, hZ, hpt ⟩ ← ih
    exact ⟨hX, hY, hZ, h_on, hpt⟩

/-- For `k > 0`, `mul_by_pow_2` of a valid point is valid and represents `2^k • self`. -/
@[step]
theorem mul_by_pow_2_spec (self : EdwardsPoint) (k : U32)
    (hself : self.IsValid) (hk : k.val > 0) :
    mul_by_pow_2 self k ⦃ (result : EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (2 ^ k.val) • self.toPoint ⦄ := by
  unfold mul_by_pow_2
  let* ⟨ hk2 ⟩ ← massert_spec
  let* ⟨ s, s_post1, s_post2, s_post3 ⟩ ← as_projective_spec
  let* ⟨ s1, h_s1_on, h_s1_X, h_s1_Y, h_s1_Z, h_s1_point ⟩ ← mul_by_pow_2_loop_spec
  -- P₀: reference point for loop invariant
  · exact self.toPoint
  -- s.OnCurve: inherit from self.OnCurve via s_post1/2/3
  · exact {
      Z_ne_zero := by rw [s_post3]; exact hself.Z_ne_zero
      on_curve := by rw [s_post1, s_post2, s_post3]; exact hself.on_curve
    }
  -- s.X[j]! < 2^53
  · intro j hj; rw [s_post1]; exact hself.X_bounds j hj
  -- s.Y[j]! < 2^53
  · intro j hj; rw [s_post2]; exact hself.Y_bounds j hj
  -- s.Z.IsValid
  · rw [s_post3]
    exact FieldElement51.IsValid_of_lt_pow hself.Z_bounds (by decide)
  -- s.toPoint' _ = 2^0 • self.toPoint = self.toPoint
  · show s.toPoint' _ = _
    simp only [show ((0#u32 : U32).val) = 0 from rfl, pow_zero, one_nsmul]
    unfold EdwardsPoint.toPoint
    rw [dif_pos hself]
    simp only [ProjectivePoint.toPoint', s_post1, s_post2, s_post3, EdwardsPoint.toPoint']
  -- Main goal: apply final double + as_extended using existential specs
  obtain ⟨cp, hcp_run, hcp_valid, hcp_eq⟩ :=
    double_spec_core s1 h_s1_on h_s1_X h_s1_Y h_s1_Z
  simp only [hcp_run, Std.bind_ok]
  apply WP.spec_mono (CompletedPoint.as_extended_spec cp hcp_valid)
  intro result ⟨_, _, _, _, _, _, _, _, h_result_valid, h_result_toPoint⟩
  refine ⟨h_result_valid, ?_⟩
  rw [h_result_toPoint, hcp_eq, h_s1_point]
  -- 2^(k-1) • P + 2^(k-1) • P = 2^k • P
  rw [← two_nsmul, ← mul_smul]
  fcongr 1
  rw [show k.val = (k.val - 1) + 1 from by omega, pow_succ, mul_comm]
  agrind

end curve25519_dalek.edwards.EdwardsPoint
