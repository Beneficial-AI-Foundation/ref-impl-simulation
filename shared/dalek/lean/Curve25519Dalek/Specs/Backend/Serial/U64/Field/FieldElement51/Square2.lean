/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K

/-! # `FieldElement51::square2`

Computes twice the square of a field element, in `𝔽_p` with `p = 2^255 - 19`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"

Port note (ref-impl-simulation, Aeneas d119a474): in `square2_loop_spec`, the overflow goal
states the index bound and rewrites `getElem!` with `getElem!_pos`, as `AddAssign.lean` does.
Two length side goals use `scalar_tac` without `List.Vector.length_val`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP


namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- For `i ≤ 5`, if `square[j] * 2 ≤ U64.max` for `i ≤ j < 5`: each limb `j ≥ i` is doubled
and each limb `j < i` is unchanged. -/
@[step]
theorem square2_loop_spec (square : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (h_no_overflow : ∀ j < 5, i.val ≤ j → square[j]!.val * 2 ≤ U64.max) :
    square2_loop square i ⦃ (result : FieldElement51) =>
      (∀ j < 5, i.val ≤ j → result[j]!.val = square[j]!.val * 2) ∧
      (∀ j < 5, j < i.val → result[j]! = square[j]!) ⦄ := by
  unfold square2_loop
  split
  · let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
    let* ⟨ i2, i2_post ⟩ ← U64.mul_spec
    case hmax =>
      have h := h_no_overflow i.val (by scalar_tac) (le_refl _)
      have hi5 : i.val < (↑square : List U64).length := by simp; scalar_tac
      simp only [Array.getElem!_Nat_eq, getElem!_pos (↑square : List U64) i.val hi5] at h
      rw [i1_post]; scalar_tac
    let* ⟨ a, a_post ⟩ ← Array.update_spec
    let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
    let* ⟨ result, result_post1, result_post2 ⟩ ← square2_loop_spec
    case h_no_overflow =>
      intro j hj hj2
      have hne : j ≠ i.val := by scalar_tac
      have := Array.set_of_ne_getElem! square i2 j i.val (by scalar_tac) (by scalar_tac) hne
      rw [a_post, show square.set i i2 = square.set (i.val)#usize i2 from rfl, this]
      exact h_no_overflow j hj (by scalar_tac)
    refine ⟨fun j _ _ ↦ ?_, fun j _ _ ↦ ?_⟩
    · rcases (show j = i.val ∨ i.val + 1 ≤ j by omega) with rfl | hlt
      · rw [result_post2 i.val (by scalar_tac) (by scalar_tac), a_post, Array.getElem!_Nat_eq,
          Array.set_val_eq,
          getElem!_pos _ _
            (by simp only [List.length_set]; scalar_tac),
          List.getElem_set_self]
        rw [i2_post, i1_post, Array.getElem!_Nat_eq,
          getElem!_pos _ _
            (by scalar_tac)]
      · rw [result_post1 j (by scalar_tac) (by scalar_tac), a_post,
          show square.set i i2 = square.set (i.val)#usize i2 from rfl,
          Array.set_of_ne_getElem! square i2 j i.val (by scalar_tac) (by scalar_tac) (by omega)]
    · have := result_post2 j (by omega) (by omega)
      simp_all
  · simp only [step_simps]
    grind
  termination_by 5 - i.val
  decreasing_by scalar_tac

/-- For limbs `< 2^54`: `result ≡ 2 · self^2 (mod p)`, with output limbs `< 2^53`. -/
@[step]
theorem square2_spec (self : Array U64 5#usize) (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square2 self ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (2 * (Field51_as_Nat self) ^ 2) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 53) ⦄ := by
  unfold square2
  let* ⟨ square, square_post2, square_post1 ⟩ ← pow2k_spec
  let* ⟨ result, result_post1, result_post2 ⟩ ← square2_loop_spec
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have : Field51_as_Nat result = 2 * Field51_as_Nat square := by
      unfold Field51_as_Nat
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have := result_post1 x (Finset.mem_range.mp hx) (by omega)
      rw [this]; ring
    grind [Nat.ModEq, Nat.mul_mod]
  · have := result_post1 i hi (by omega)
    have := square_post1 i hi
    omega

end curve25519_dalek.backend.serial.u64.field.FieldElement51
