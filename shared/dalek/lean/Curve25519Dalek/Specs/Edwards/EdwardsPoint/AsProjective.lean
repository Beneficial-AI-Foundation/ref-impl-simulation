/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# `EdwardsPoint::as_projective`

`as_projective` maps extended coordinates `(X, Y, Z, T)` to projective coordinates `(X, Y, Z)`.
It drops `T`.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.EdwardsPoint

/-- `as_projective self` has the same `X`, `Y` and `Z` as `self`. -/
@[step]
theorem as_projective_spec (self : EdwardsPoint) :
    as_projective self ⦃ (result : backend.serial.curve_models.ProjectivePoint) =>
      result.X = self.X ∧
      result.Y = self.Y ∧
      result.Z = self.Z ⦄ := by
  unfold as_projective
  simp

end curve25519_dalek.edwards.EdwardsPoint
