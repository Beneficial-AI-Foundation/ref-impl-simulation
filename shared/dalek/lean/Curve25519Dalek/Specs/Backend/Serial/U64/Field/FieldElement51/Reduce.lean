/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Curve25519Dalek.Auxiliary
import Mathlib.Tactic.IntervalCases

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::reduce`

This function performs a single weak reduction step on a `FieldElement51` whose limbs may
have grown beyond `2 ^ 51`. It propagates carries through the limbs and finally folds the
top-limb overflow back into the bottom limb using the prime relation `2^255 ≡ 19 (mod p)`,
returning a representation with limbs `< 2 ^ 52` and value `< 2 * p`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"

Port note (ref-impl-simulation, Aeneas d119a474): the proof is new. It splits `reduce` in two
stages (`reduce_carries`, `reduce_add`) so that it fits in the default heartbeats, and it
moves the arithmetic to `reduce_arith`. The statement of `reduce_spec` is unchanged.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

attribute [-simp] Int.reducePow Nat.reducePow

/-- **Spec theorem for `reduce.LOW_51_BIT_MASK`**
• The function always succeeds (no panic)
• The result equals `2 ^ 51 - 1`
-/
@[step]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ (result : U64) =>
      result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  step*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Stages

`reduce` is split in two stages, so that each proof stays within the default heartbeats. -/

/-- Stage 1: the carries and the masked limbs. -/
def reduce_carries (limbs : Array U64 5#usize) :
    Result (Array U64 5#usize × U64 × U64 × U64 × U64 × U64) := do
  let i ← Array.index_usize limbs 0#usize
  let c0 ← i >>> 51#i32
  let i1 ← Array.index_usize limbs 1#usize
  let c1 ← i1 >>> 51#i32
  let i2 ← Array.index_usize limbs 2#usize
  let c2 ← i2 >>> 51#i32
  let i3 ← Array.index_usize limbs 3#usize
  let c3 ← i3 >>> 51#i32
  let i4 ← Array.index_usize limbs 4#usize
  let c4 ← i4 >>> 51#i32
  let i5 ← reduce.LOW_51_BIT_MASK
  let i6 ← lift (i &&& i5)
  let limbs1 ← Array.update limbs 0#usize i6
  let i7 ← Array.index_usize limbs1 1#usize
  let i8 ← lift (i7 &&& i5)
  let limbs2 ← Array.update limbs1 1#usize i8
  let i9 ← Array.index_usize limbs2 2#usize
  let i10 ← lift (i9 &&& i5)
  let limbs3 ← Array.update limbs2 2#usize i10
  let i11 ← Array.index_usize limbs3 3#usize
  let i12 ← lift (i11 &&& i5)
  let limbs4 ← Array.update limbs3 3#usize i12
  let i13 ← Array.index_usize limbs4 4#usize
  let i14 ← lift (i13 &&& i5)
  let limbs5 ← Array.update limbs4 4#usize i14
  ok (limbs5, c0, c1, c2, c3, c4)

/-- Stage 2: add the carries to the next limbs. -/
def reduce_add (limbs5 : Array U64 5#usize) (c0 c1 c2 c3 c4 : U64) :
    Result (Array U64 5#usize) := do
  let i15 ← c4 * 19#u64
  let i16 ← Array.index_usize limbs5 0#usize
  let i17 ← i16 + i15
  let limbs6 ← Array.update limbs5 0#usize i17
  let i18 ← Array.index_usize limbs6 1#usize
  let i19 ← i18 + c0
  let limbs7 ← Array.update limbs6 1#usize i19
  let i20 ← Array.index_usize limbs7 2#usize
  let i21 ← i20 + c1
  let limbs8 ← Array.update limbs7 2#usize i21
  let i22 ← Array.index_usize limbs8 3#usize
  let i23 ← i22 + c2
  let limbs9 ← Array.update limbs8 3#usize i23
  let i24 ← Array.index_usize limbs9 4#usize
  let i25 ← i24 + c3
  let limbs10 ← Array.update limbs9 4#usize i25
  ok limbs10

set_option maxRecDepth 4096 in
/-- `reduce` in terms of the two stages. -/
theorem reduce_unfold (limbs : Array U64 5#usize) :
    reduce limbs =
      (do let r ← reduce_carries limbs
          reduce_add r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2) := by
  rw [reduce]
  simp only [reduce_carries, reduce_add, Std.bind_assoc, Std.bind_ok]

private theorem getElem!_eq_list_getElem (a : Array U64 5#usize) (k : ℕ) (hk : k < 5) :
    a[k]! = (↑a : List U64)[k]'(by simp [hk]) := by
  simp [Array.getElem!_Nat_eq, hk]

private theorem land_mask51 (x : ℕ) : x &&& 2251799813685247 = x % 2251799813685248 :=
  Nat.and_two_pow_sub_one_eq_mod x 51

theorem reduce_carries_spec (limbs : Array U64 5#usize) :
    reduce_carries limbs ⦃ r =>
      (∀ k < 5, r.1[k]!.val = limbs[k]!.val % 2 ^ 51) ∧
      r.2.1.val = limbs[0]!.val / 2 ^ 51 ∧ r.2.2.1.val = limbs[1]!.val / 2 ^ 51 ∧
      r.2.2.2.1.val = limbs[2]!.val / 2 ^ 51 ∧ r.2.2.2.2.1.val = limbs[3]!.val / 2 ^ 51 ∧
      r.2.2.2.2.2.val = limbs[4]!.val / 2 ^ 51 ⦄ := by
  unfold reduce_carries
  step*
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    subst_vars
    interval_cases k <;>
      simp_all [UScalar.val_and, land_mask51]
  all_goals simp [*, Nat.shiftRight_eq_div_pow]

/-- The arithmetic of `reduce` on natural numbers. -/
private theorem reduce_arith (l0 l1 l2 l3 l4 : ℕ) (h0 : l0 < 2 ^ 64) (h1 : l1 < 2 ^ 64)
    (h2 : l2 < 2 ^ 64) (h3 : l3 < 2 ^ 64) (h4 : l4 < 2 ^ 64) :
    l0 % 2 ^ 51 + l4 / 2 ^ 51 * 19 < 2 ^ 52 ∧ l1 % 2 ^ 51 + l0 / 2 ^ 51 < 2 ^ 52 ∧
    l2 % 2 ^ 51 + l1 / 2 ^ 51 < 2 ^ 52 ∧ l3 % 2 ^ 51 + l2 / 2 ^ 51 < 2 ^ 52 ∧
    l4 % 2 ^ 51 + l3 / 2 ^ 51 < 2 ^ 52 ∧
    (l0 % 2 ^ 51 + l4 / 2 ^ 51 * 19) + 2 ^ 51 * (l1 % 2 ^ 51 + l0 / 2 ^ 51) +
      2 ^ 102 * (l2 % 2 ^ 51 + l1 / 2 ^ 51) + 2 ^ 153 * (l3 % 2 ^ 51 + l2 / 2 ^ 51) +
      2 ^ 204 * (l4 % 2 ^ 51 + l3 / 2 ^ 51) + l4 / 2 ^ 51 * p =
      l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 ∧
    (l0 % 2 ^ 51 + l4 / 2 ^ 51 * 19) + 2 ^ 51 * (l1 % 2 ^ 51 + l0 / 2 ^ 51) +
      2 ^ 102 * (l2 % 2 ^ 51 + l1 / 2 ^ 51) + 2 ^ 153 * (l3 % 2 ^ 51 + l2 / 2 ^ 51) +
      2 ^ 204 * (l4 % 2 ^ 51 + l3 / 2 ^ 51) < 2 * p := by
  unfold p
  omega

theorem reduce_add_spec (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U64)
    (ha : ∀ k < 5, a[k]!.val < 2 ^ 51) (h0 : c0.val < 2 ^ 13) (h1 : c1.val < 2 ^ 13)
    (h2 : c2.val < 2 ^ 13) (h3 : c3.val < 2 ^ 13) (h4 : c4.val < 2 ^ 13) :
    reduce_add a c0 c1 c2 c3 c4 ⦃ r =>
      r[0]!.val = a[0]!.val + c4.val * 19 ∧ r[1]!.val = a[1]!.val + c0.val ∧
      r[2]!.val = a[2]!.val + c1.val ∧ r[3]!.val = a[3]!.val + c2.val ∧
      r[4]!.val = a[4]!.val + c3.val ⦄ := by
  have ha0 := ha 0 (by decide)
  have ha1 := ha 1 (by decide)
  have ha2 := ha 2 (by decide)
  have ha3 := ha 3 (by decide)
  have ha4 := ha 4 (by decide)
  simp only [getElem!_eq_list_getElem _ _ (by decide : (0 : ℕ) < 5),
    getElem!_eq_list_getElem _ _ (by decide : (1 : ℕ) < 5),
    getElem!_eq_list_getElem _ _ (by decide : (2 : ℕ) < 5),
    getElem!_eq_list_getElem _ _ (by decide : (3 : ℕ) < 5),
    getElem!_eq_list_getElem _ _ (by decide : (4 : ℕ) < 5)] at ha0 ha1 ha2 ha3 ha4 ⊢
  clear ha
  unfold reduce_add
  step*
  all_goals (subst_vars; simp_all <;> scalar_tac)

/-- `Field51_as_Nat` as an explicit sum of five limbs. -/
theorem Field51_as_Nat_expand (a : Array U64 5#usize) :
    Field51_as_Nat a = a[0]!.val + 2 ^ 51 * a[1]!.val + 2 ^ 102 * a[2]!.val +
      2 ^ 153 * a[3]!.val + 2 ^ 204 * a[4]!.val := by
  simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::reduce`**
• The function always succeeds (no panic) on any 5-limb input
• Every output limb is `< 2 ^ 52`
• `Field51_as_Nat limbs ≡ Field51_as_Nat result (mod p)`, i.e. value is preserved modulo `p`
• `Field51_as_Nat result < 2 * p`, i.e. weakly reduced
-/
@[step]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (result : FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] ∧
      Field51_as_Nat result < 2 * p ⦄ := by
  rw [reduce_unfold]
  step with reduce_carries_spec as ⟨r, hr, hc0, hc1, hc2, hc3, hc4⟩
  have hb : ∀ k : ℕ, (limbs[k]! : U64).val < 2 ^ 64 := fun k => by scalar_tac
  step with reduce_add_spec as ⟨res, e0, e1, e2, e3, e4⟩
  obtain ⟨b0, b1, b2, b3, b4, heq, hlt⟩ :=
    reduce_arith _ _ _ _ _ (hb 0) (hb 1) (hb 2) (hb 3) (hb 4)
  rw [hr 0 (by decide), hc4] at e0
  rw [hr 1 (by decide), hc0] at e1
  rw [hr 2 (by decide), hc1] at e2
  rw [hr 3 (by decide), hc2] at e3
  rw [hr 4 (by decide), hc3] at e4
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> omega
  · rw [Field51_as_Nat_expand, Field51_as_Nat_expand, e0, e1, e2, e3, e4]
    exact (modeq_of_add_mul_eq _ _ _ _ heq).symm
  · rw [Field51_as_Nat_expand, e0, e1, e2, e3, e4]
    exact hlt

end curve25519_dalek.backend.serial.u64.field.FieldElement51
