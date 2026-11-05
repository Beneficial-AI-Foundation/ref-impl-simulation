/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul

/-!
# `CompletedPoint::as_extended`

`as_extended` maps a `CompletedPoint` `(X, Y, Z, T)`, which represents `(X/Z, Y/T)`, to the
`EdwardsPoint` `(X·T, Y·Z, Z·T, X·Y)`. An `EdwardsPoint` `(X', Y', Z', T')` represents
`(X'/Z', Y'/Z')` with `T' = X'·Y'/Z'`.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"

Port note (ref-impl-simulation, Aeneas d119a474): `toPoint` maps to
`DalekSim.Edwards.Point dEd`. So the proof uses `Edwards.lift_mod_eq_iff` in place of
`Montgomery.lift_mod_eq_iff` and `Point.mk'_inj` in place of `Point.mk.injEq`, and the import of
`Math/Montgomery/Curve.lean` is dropped.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-- For valid `q`, `as_extended q` returns a valid `e = (X·T, Y·Z, Z·T, X·Y)` mod `p` with
limbs `< 2^52` and `e.toPoint = q.toPoint`. -/
@[step]
theorem as_extended_spec (q : CompletedPoint)
    (h_q_Valid : q.IsValid) :
    as_extended q ⦃ (e : edwards.EdwardsPoint) =>
      let X := Field51_as_Nat q.X
      let Y := Field51_as_Nat q.Y
      let Z := Field51_as_Nat q.Z
      let T := Field51_as_Nat q.T
      let X' := Field51_as_Nat e.X
      let Y' := Field51_as_Nat e.Y
      let Z' := Field51_as_Nat e.Z
      let T' := Field51_as_Nat e.T
      X' % p = (X * T) % p ∧
      Y' % p = (Y * Z) % p ∧
      Z' % p = (Z * T) % p ∧
      T' % p = (X * Y) % p ∧
      (∀ i < 5, e.X[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, e.Y[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, e.Z[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, e.T[i]!.val < 2 ^ 52) ∧
      e.IsValid ∧
      e.toPoint = q.toPoint ⦄ := by
  unfold as_extended
  have := h_q_Valid.X_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  have := h_q_Valid.Y_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  have := h_q_Valid.Z_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  have := h_q_Valid.T_valid
  simp only [FieldElement51.IsValid, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
  simp only [step_simps]
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  rw [← Nat.ModEq,← Nat.ModEq,← Nat.ModEq, ← Nat.ModEq]
  simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem?_pos, Option.getD_some,
    Array.getElem!_Nat_eq, getElem!_pos, Nat.reducePow, implies_true, true_and]
  rw[Edwards.lift_mod_eq_iff] at fe_post1
  rw[Edwards.lift_mod_eq_iff] at fe1_post1
  rw[Edwards.lift_mod_eq_iff] at fe2_post1
  rw[Edwards.lift_mod_eq_iff] at fe3_post1
  have :({ X := fe, Y := fe1, Z := fe2, T := fe3 }:edwards.EdwardsPoint).IsValid := by
    refine
      { Z_ne_zero := ?_, T_relation := ?_, on_curve := ?_,
        X_bounds := ?_, Y_bounds := ?_, Z_bounds := ?_, T_bounds := ?_ }
    · have := h_q_Valid.T_ne_zero
      unfold FieldElement51.toField at this
      have := h_q_Valid.Z_ne_zero
      unfold FieldElement51.toField at this
      unfold FieldElement51.toField
      simp only [fe2_post1, Nat.cast_mul, ne_eq, mul_eq_zero, not_or]
      grind
    · simp only
      unfold FieldElement51.toField
      grind
    · simp only
      have :=  h_q_Valid.on_curve
      unfold FieldElement51.toField at this
      simp only at this
      unfold FieldElement51.toField
      grind
    · intro i hi; grind [Array.getElem!_Nat_eq, Array.val_getElem!_eq']
    · intro i hi; grind [Array.getElem!_Nat_eq, Array.val_getElem!_eq']
    · intro i hi; grind [Array.getElem!_Nat_eq, Array.val_getElem!_eq']
    · intro i hi; grind [Array.getElem!_Nat_eq, Array.val_getElem!_eq']
  simp only [this, true_and]
  unfold toPoint   edwards.EdwardsPoint.toPoint
  simp only [this, ↓reduceDIte, h_q_Valid]
  unfold toPoint' edwards.EdwardsPoint.toPoint'
  simp only [DalekSim.Edwards.Point.mk'_inj]
  unfold FieldElement51.toField
  have := h_q_Valid.T_ne_zero
  unfold FieldElement51.toField at this
  have := h_q_Valid.Z_ne_zero
  unfold FieldElement51.toField at this
  simp_all only [Nat.cast_mul, ne_eq]
  grind

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
