/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Filippo A. E. Nuccio, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended

/-!
# `EdwardsPoint::double`

`double` computes `P + P` for an Edwards point `P`.

Source: "curve25519-dalek/src/edwards.rs"

Port note (ref-impl-simulation, Aeneas d119a474): the bind after `double` is reduced with
`Std.bind_ok`, and the point equality uses `DalekSim.Edwards.Point.ext_xy` in place of
`congr 1`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
  curve25519_dalek.backend.serial.curve_models.ProjectivePoint
  curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.edwards.EdwardsPoint

-- Mark `p` as irreducible locally so that algebraic reasoning about the
-- curve equation does not unfold the prime modulus.
attribute [local irreducible] p in
/-- `double` of a valid point is valid and represents `P + P`. -/
@[step]
theorem double_spec (self : EdwardsPoint) (hself : self.IsValid) :
    double self ⦃ (result : EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint + self.toPoint ⦄ := by
  unfold double
  -- Step 1: as_projective (preserves X, Y, Z)
  apply WP.spec_bind
    (as_projective_spec self)
  intro pp ⟨hpp_X, hpp_Y, hpp_Z⟩
  -- Build pp.OnCurve from self.IsValid
  have hpp_on : pp.OnCurve := {
    Z_ne_zero := by rw [hpp_Z]; exact hself.Z_ne_zero
    on_curve := by rw [hpp_X, hpp_Y, hpp_Z]; exact hself.on_curve
  }
  -- Step 2: double via core theorem (existential form)
  obtain ⟨cp, h_run, h_cp_valid, h_cp_eq⟩ :=
    double_spec_core pp hpp_on
      (fun i hi => by rw [hpp_X]; exact hself.X_bounds i hi)
      (fun i hi => by rw [hpp_Y]; exact hself.Y_bounds i hi)
      (by rw [hpp_Z]
          exact FieldElement51.IsValid_of_lt_pow
            hself.Z_bounds (by decide))
  -- Thread pp.double = ok cp through the WP chain
  simp only [h_run, Std.bind_ok]
  -- Step 3: as_extended (preserves the point)
  apply WP.spec_mono
    (CompletedPoint.as_extended_spec cp h_cp_valid)
  intro result
    ⟨_, _, _, _, _, _, _, _,
     h_result_valid, h_result_toPoint⟩
  exact ⟨h_result_valid, by
    rw [h_result_toPoint, h_cp_eq]
    apply DalekSim.Edwards.Point.ext_xy <;>
      simp only [ProjectivePoint.toPoint',
        hpp_X, hpp_Y, hpp_Z,
        EdwardsPoint.toPoint, dif_pos hself,
        EdwardsPoint.toPoint']⟩

end curve25519_dalek.edwards.EdwardsPoint
