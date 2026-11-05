/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg

/-! # `AffineNielsPoint::neg`

Negates an affine Niels point `(y+x, y−x, 2dxy)`. It swaps `y_plus_x` and `y_minus_x` and
negates `xy2d`.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
namespace curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint

/-- For `xy2d` limbs `< 2^54`: `y_plus_x` and `y_minus_x` are swapped, and
`self.xy2d + result.xy2d ≡ 0 (mod p)`. -/
@[step]
theorem neg_spec
    (self : backend.serial.curve_models.AffineNielsPoint)
    (self_bound : ∀ i < 5, self.xy2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : AffineNielsPoint) =>
      result.y_plus_x = self.y_minus_x ∧
      result.y_minus_x = self.y_plus_x ∧
      (Field51_as_Nat self.xy2d + Field51_as_Nat result.xy2d) % p = 0 ⦄ := by
  unfold neg
  step*
  simp_all [Nat.ModEq]

end curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace CoreOpsArithNegAffineNielsPoint

/-- Owned-value form of the shared-reference `neg_spec`, with the same statement. -/
@[step]
theorem neg_spec
    (self : backend.serial.curve_models.AffineNielsPoint)
    (self_bound : ∀ i < 5, self.xy2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : AffineNielsPoint) =>
      result.y_plus_x = self.y_minus_x ∧
      result.y_minus_x = self.y_plus_x ∧
      (Field51_as_Nat self.xy2d + Field51_as_Nat result.xy2d) % p = 0 ⦄ := by
  unfold neg
  exact Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg_spec
    self self_bound

end CoreOpsArithNegAffineNielsPoint
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
