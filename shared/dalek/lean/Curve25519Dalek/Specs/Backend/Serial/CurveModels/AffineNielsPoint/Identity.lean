/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-! # `AffineNielsPoint::identity`

Returns the identity `(x, y) = (0, 1)` in affine Niels coordinates `(y+x, y−x, 2dxy) = (1, 1, 0)`.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace Curve25519_dalekTraitsIdentity

/-- The identity has `y_plus_x = 1`, `y_minus_x = 1` and `xy2d = 0`. -/
@[step]
theorem identity_spec :
    identity ⦃ (q : AffineNielsPoint) =>
      Field51_as_Nat q.y_plus_x = 1 ∧
      Field51_as_Nat q.y_minus_x = 1 ∧
      Field51_as_Nat q.xy2d = 0 ⦄ := by
  unfold identity
  step*

end Curve25519_dalekTraitsIdentity
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
