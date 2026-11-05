/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Negate

/-! # `FieldElement51::neg`

Field negation. It calls `negate`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field FieldElement51
namespace curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51

/-- For limbs `< 2^54`: `self + neg ≡ 0 (mod p)`, with output limbs `< 2^52`. -/
@[step]
theorem neg_spec (self : FieldElement51)
    (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    neg self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val < 2 ^ 52 ⦄ := by
  unfold neg
  step*

end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
