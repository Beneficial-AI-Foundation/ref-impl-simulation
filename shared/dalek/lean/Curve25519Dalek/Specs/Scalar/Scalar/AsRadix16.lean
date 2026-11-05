/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Auxiliary

/-!
# Spec of `curve25519_dalek::scalar::Scalar::as_radix_16`

`as_radix_16` recodes a scalar `s = ∑ i < 32, 256^i · b_i` into 64 signed digits `d_i` with
`s = ∑ i < 64, 16^i · d_i`, in three steps.

1. `massert (self[31] ≤ 127)` checks that `s < 2^255`.
2. Loop 0 (`as_radix_16_loop0`) sets `d_(2i) = b_i % 16` and `d_(2i+1) = b_i / 16` for `i < 32`.
   Each byte keeps its value, because `(b % 16) · 16^(2i) + (b / 16) · 16^(2i+1) = b · 256^i`.
   All digits are then in `[0, 15]`.
3. Loop 1 (`as_radix_16_loop1`) sets, for `i < 63`, `c = (d_i + 8) >> 4`, `d_i ← d_i - 16 c` and
   `d_(i+1) ← d_(i+1) + c`. Then `c ∈ {0, 1}` and `d_i ∈ [-8, 7]`. The value does not change,
   because `(d - 16 c) · 16^i + (d' + c) · 16^(i+1) = d · 16^i + d' · 16^(i+1)`.

Loop 1 gives `0 ≤ d_63 ≤ 16`. Because `s < 2^255 = 8 · 16^63`, the value equation gives
`d_63 ≤ 8` (`digit_63_le_8`). `as_radix_16_spec` states the bound `8`.

Source: "curve25519-dalek/src/scalar.rs"

## Port note

This file ports the file of curve25519-dalek-lean-verify `26d49052` to Aeneas `d119a474`.
The extracted code of `as_radix_16` is the same as upstream.

- `as_radix_16_spec` states `d_63 ≤ 8`. Upstream states `d_63 ≤ 16` and proves the bound `8` in
  a caller. `digit_63_le_8` is upstream `scalar_digit_63_le_8` from `VariableBase/Mul.lean`, and
  `U8x32_as_Nat_lt_pow255` comes from upstream `AsRadix2w.lean`.
- The exit cases of the two loops rewrite with `WP.spec_ok` before they split the conjunction.
- In `i8_shiftRight_4_spec`, a `simp only` reduces the `if` on the shift amount, and `erw`
  replaces `rw` for `BitVec.toInt_ofInt`, because the width of `toInt` is
  `IScalarTy.I8.numBits` and not the literal `8`. The lemma proves the value once and gets the
  bounds from it. Upstream names it `isize_shiftRight_4_spec`.
- The loop specs are the recursive theorems. Upstream proves private `_strong` theorems with the
  same statements. The unused lemmas `carry_recenter_identity` and `lo_bounds_step` are removed.

The precondition `self.bytes[31] ≤ 127` is the `debug_assert!` of the Rust code, which Aeneas
extracts as `massert`. It is Invariant #1 of `Scalar`. A clamped scalar meets it, because
`clamp_integer` clears bit 7 of byte 31. A canonical scalar meets it, because it is less than
`ℓ < 2^253`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
attribute [-simp] Int.reducePow Nat.reducePow
namespace curve25519_dalek.scalar.Scalar.as_radix_16

/-- `bot_half x` succeeds and returns `x % 16`, which is at most `15`. -/
@[step]
theorem bot_half_spec (x : U8) :
    bot_half x ⦃ (result : U8) =>
      result.val = x.val % 16 ∧
      result.val ≤ 15 ⦄ := by
  unfold bot_half
  step as ⟨i, hi_val, _⟩
  have hx_bound : x.val < 256 := x.hBounds
  have hi_eq : i.val = x.val := by
    rw [hi_val, Nat.shiftRight_eq_div_pow]
    norm_num
  have h15 : (15#u8 : U8).val = 15 := by decide
  have hmod_lt : x.val % 16 ≤ 15 := by omega
  have hland : x.val &&& 15 = x.val % 16 := by
    have h := land_pow_two_sub_one_eq_mod x.val 4
    norm_num at h
    exact h
  simp [step_simps, UScalar.val_and, hi_eq, h15, hland]
  omega

/-- `top_half x` succeeds and returns `x / 16`, which is at most `15`. -/
@[step]
theorem top_half_spec (x : U8) :
    top_half x ⦃ (result : U8) =>
      result.val = x.val / 16 ∧
      result.val ≤ 15 ⦄ := by
  unfold top_half
  step as ⟨i, hi_val, _⟩
  have hx_bound : x.val < 256 := x.hBounds
  have hi_eq : i.val = x.val / 16 := by
    rw [hi_val, Nat.shiftRight_eq_div_pow]
  have h15 : (15#u8 : U8).val = 15 := by decide
  have hdiv_lt : x.val / 16 < 16 := Nat.div_lt_of_lt_mul (by omega)
  have hland : x.val / 16 &&& 15 = x.val / 16 := by
    have h := land_pow_two_sub_one_eq_mod (x.val / 16) 4
    norm_num at h
    rw [h, Nat.mod_eq_of_lt hdiv_lt]
  simp [step_simps, UScalar.val_and, hi_eq, h15, hland]
  omega

end curve25519_dalek.scalar.Scalar.as_radix_16

namespace curve25519_dalek.scalar.Scalar

/-- The integer `∑ i < 64, 16^i · digits[i]` of an array of signed radix-16 digits. -/
def I8x64_as_Radix16 (digits : Array I8 64#usize) : ℤ :=
  ∑ i ∈ Finset.range 64, (16 : ℤ)^i * (digits[i]!).val

/-! ## Loop 0 -/

private lemma nibble_identity (b i : ℕ) :
    (↑(b % 16) : ℤ) * (16 : ℤ) ^ (2 * i) + (↑(b / 16) : ℤ) * (16 : ℤ) ^ (2 * i + 1) =
    ↑b * (256 : ℤ) ^ i := by
  have h256 : (16 : ℤ) ^ (2 * i) = (256 : ℤ) ^ i := by
    rw [pow_mul]
    ring_nf
  have h16 : (16 : ℤ) ^ (2 * i + 1) = 16 * (256 : ℤ) ^ i := by
    rw [pow_succ, h256]; ring
  have hb : (↑b : ℤ) = ↑(b % 16) + 16 * ↑(b / 16) := by
    push_cast
    have := Nat.div_add_mod b 16
    omega
  rw [h256, h16, hb]
  ring

@[step]
private lemma I8x64_update_get (arr : Array I8 64#usize) (j : Usize)
    (v : I8) (hj : j.val < 64) :
    Array.update arr j v ⦃ (arr' : Array I8 64#usize) =>
    (∀ (k : ℕ), (hk : k ≠ j.val) → (arr')[k]! = arr[k]!) ∧
    (arr')[j.val]! = v ⦄ := by
  have hbound : j.val < arr.length := by scalar_tac
  apply spec_mono (Array.update_spec arr j v hbound)
  intro arr' harr'
  subst harr'
  constructor
  · intro k hk
    simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    simp [hk]
  · simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    rw [getElem!_pos _ _ (by simpa using hbound), List.getElem_set_self]

private lemma inv_step
    (self : Scalar) (output a : Array I8 64#usize) (i : ℕ)
    (i4 : I8) (hi4 : i4.val = ↑((self.bytes[i]!).val % 16))
    (i7 : I8) (hi7 : i7.val = ↑((self.bytes[i]!).val / 16))
    (ha_even : (a)[2 * i]! = i4)
    (ha_odd : (a)[2 * i + 1]! = i7)
    (ha_pref : ∀ j < 2 * i, (a[j]! : I8).val = (output[j]!).val)
    (h_inv : ∑ j ∈ Finset.range (2 * i), (16 : ℤ) ^ j * (output[j]!).val =
             ↑(∑ k ∈ Finset.range i, 2 ^ (8 * k) * (self.bytes[k]!).val)) :
    ∑ j ∈ Finset.range (2 * (i + 1)), (16 : ℤ) ^ j * (a[j]!).val =
    ↑(∑ k ∈ Finset.range (i + 1), 2 ^ (8 * k) * (self.bytes[k]!).val) := by
  have h2i1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
  rw [h2i1, Finset.sum_range_succ, show 2 * i + 1 = 2 * i + 0 + 1 from by ring,
      Finset.sum_range_succ]
  have ha_odd_val : ((a)[2 * i + 1]!).val = ↑((self.bytes[i]!).val / 16) := by
    rw [ha_odd]; exact hi7
  have ha_even_val : ((a)[2 * i]!).val = ↑((self.bytes[i]!).val % 16) := by
     rw [ha_even]; exact hi4
  have h_pref_sum : ∑ j ∈ Finset.range (2 * i), (16 : ℤ) ^ j * (a[j]!).val =
                    ∑ j ∈ Finset.range (2 * i), (16 : ℤ) ^ j * (output[j]!).val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ha_pref j (Finset.mem_range.mp hj)]
  rw [h_pref_sum, h_inv, ha_even_val, ha_odd_val]
  push_cast [Finset.sum_range_succ]
  have h_nibble := nibble_identity (self.bytes[i]!).val i
  simp only [Array.getElem!_Nat_eq, add_zero, add_assoc, add_right_inj]
  simp only [Array.getElem!_Nat_eq, Int.natCast_emod, Nat.cast_ofNat, mul_comm, Int.natCast_ediv]
    at h_nibble
  simp only [mul_comm]
  rw [h_nibble]
  simp only [mul_eq_mul_right_iff, Int.natCast_eq_zero]
  left
  have h256 : (2 : ℤ) ^ (8 * i) = (256 : ℤ) ^ i := by
    rw [show (256 : ℤ) = 2 ^ 8 from by norm_num, ← pow_mul]
  grind

private lemma tail_step
    (output a : Array I8 64#usize) (i : ℕ)
    (ha_later : ∀ j, 2 * (i + 1) ≤ j → j < 64 → (a[j]! : I8).val = (output[j]!).val)
    (h_tail : ∀ j, 2 * i ≤ j → j < 64 → (output[j]! : I8).val = 0) :
    ∀ j, 2 * (i + 1) ≤ j → j < 64 → (a[j]! : I8).val = 0 := by
  intro j hj1 hj2
  rw [ha_later j hj1 hj2]
  exact h_tail j (by omega) hj2

private lemma bounds_step
    (output a : Array I8 64#usize) (i : ℕ)
    (i4 i7 : I8)
    (hi4_pos : (0 : ℤ) ≤ i4.val) (hi4_le : i4.val ≤ 15)
    (hi7_pos : (0 : ℤ) ≤ i7.val) (hi7_le : i7.val ≤ 15)
    (ha_even : (a)[2 * i]! = i4)
    (ha_odd : (a)[2 * i + 1]! = i7)
    (ha_pref : ∀ j < 2 * i, (a[j]! : I8).val = (output[j]!).val)
    (h_bounds : ∀ j < 2 * i, (0 : ℤ) ≤ (output[j]!).val ∧ (output[j]!).val ≤ 15) :
    ∀ j < 2 * (i + 1), (0 : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val ≤ 15 := by
  intro j hj
  rcases lt_or_ge j (2 * i) with hlt | hge
  · have hval : (a[j]!).val = (output[j]!).val := ha_pref j hlt
    rw [hval]; exact h_bounds j hlt
  · rcases Nat.eq_or_lt_of_le hge with rfl | hlt
    · rw [ha_even]; exact ⟨hi4_pos, hi4_le⟩
    · have hj_eq : j = 2 * i + 1 := by omega
      subst hj_eq; rw [ha_odd]; exact ⟨hi7_pos, hi7_le⟩

/-- Loop 0 from index `i ≤ 32`. If the digits below `2 i` are in `[0, 15]` and have the value of
the bytes below `i`, and the other digits are `0`, then the loop succeeds and returns digits in
`[0, 15]` with the value of the scalar. -/
@[step]
theorem as_radix_16_loop0_spec
    (self : Scalar)
    (output : Array I8 64#usize)
    (i : Usize)
    (hi : i.val ≤ 32)
    (h_inv : ∑ j ∈ Finset.range (2 * i.val), (16 : ℤ) ^ j * (output[j]!).val =
             ↑(∑ k ∈ Finset.range i.val, 2 ^ (8 * k) * (self.bytes[k]!).val))
    (h_tail : ∀ j, 2 * i.val ≤ j → j < 64 → (output[j]! : I8).val = 0)
    (h_bounds : ∀ j < 2 * i.val,
        (0 : ℤ) ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    as_radix_16_loop0 self output i ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes) ∧
      ∀ k < 64, (0 : ℤ) ≤ (result[k]!).val ∧ (result[k]!).val ≤ 15 ⦄ := by
  unfold as_radix_16_loop0
  split
  case isTrue hlt =>
    have hi' : i.val < 32 := by scalar_tac
    unfold Scalar.Insts.CoreOpsIndexIndexUsizeU8.index
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2_val, hi2_le⟩
    step as ⟨i3, hi3⟩
    have h_cast2 : i2.val < 128 := by omega
    step as ⟨i4, hi4⟩
    have h_i3_lt : i3.val < 64 := by omega
    step as ⟨output1, h_upd1⟩
    step as ⟨i5, hi5_val, hi5_le⟩
    step as ⟨i6, hi6⟩
    have hi6_val : i6.val = 2 * i.val + 1 := by scalar_tac
    have h_cast5 : i5.val < 128 := by omega
    step as ⟨i7, hi7⟩
    have h_i6_lt : i6.val < 64 := by omega
    step as ⟨a, h_upd2⟩
    step as ⟨i8, hi8⟩
    have hi8_val : i8.val = i.val + 1 := by scalar_tac
    have h_hi4 : i4.val = ↑((self.bytes[i.val]!).val % 16) := by
      have h := hi2_val; rw [hi1] at h
      have hspec := UScalar.hcast_inBounds_spec .I8 i2 (by
      simp only [IScalar.max]; scalar_tac)
      simp only [lift, WP.spec_ok] at hspec
      rw [hi4, hspec]
      rw [Array.getElem!_Nat_eq, getElem!_pos _ _ (by simpa using hi')]; simp [h]
    have h_hi7 : i7.val = ↑((self.bytes[i.val]!).val / 16) := by
      have h := hi5_val; rw [hi1] at h
      have hspec := UScalar.hcast_inBounds_spec .I8 i5 (by
      simp only [IScalar.max]; scalar_tac)
      simp only [lift, WP.spec_ok] at hspec
      rw [hi7, hspec]
      rw [Array.getElem!_Nat_eq, getElem!_pos _ _ (by simpa using hi')]; simp [h]
    have ha_even : a[2 * i.val]! = i4 := by
      have h6_ne_3 : i3.val ≠ i6.val := by omega
      simp_all [h_upd2 (2 * i.val) (by omega)]
    have ha_odd : a[2 * i.val + 1]! = i7 := by
      simp_all
    have ha_pref : ∀ j < 2 * i.val, (a[j]! : I8).val = (output[j]!).val := by
      intro j hj
      have eq:= h_upd1 j
      simp only [hi3, ne_eq, Array.getElem!_Nat_eq] at eq
      have : ¬j = 2 * ↑i := by grind
      simp only [this, not_false_eq_true, forall_const] at eq
      have eq1:= h_upd2 j
      simp only [hi6_val, ne_eq, Array.getElem!_Nat_eq] at eq1
      have : ¬j = 2 * ↑i +1 := by grind
      simp only [this, not_false_eq_true, forall_const] at eq1
      simp only [Array.getElem!_Nat_eq, eq1, eq]
    have ha_later : ∀ j, 2 * (i.val + 1) ≤ j → j < 64 →
      (a[j]! : I8).val = (output[j]!).val := by
      intro j hj1 hj2
      have eq := h_upd1 j
      simp only [hi3, ne_eq, Array.getElem!_Nat_eq] at eq
      have hne1 : ¬j = 2 * ↑i := by grind
      simp only [hne1, not_false_eq_true, forall_const] at eq
      have eq1 := h_upd2 j
      simp only [hi6_val, ne_eq, Array.getElem!_Nat_eq] at eq1
      have hne2 : ¬j = 2 * ↑i + 1 := by grind
      simp only [hne2, not_false_eq_true, forall_const] at eq1
      simp only [Array.getElem!_Nat_eq, eq1, eq]
    have h_inv' : ∑ j ∈ Finset.range (2 * i8.val), (16 : ℤ) ^ j * (a[j]!).val =
                  ↑(∑ k ∈ Finset.range i8.val, 2 ^ (8 * k) * (self.bytes[k]!).val) := by
      rw [hi8_val]
      exact inv_step self output a i.val i4 h_hi4 i7 h_hi7
              ha_even ha_odd ha_pref h_inv
    have h_tail' : ∀ j, 2 * i8.val ≤ j → j < 64 → (a[j]! : I8).val = 0 := by
      rw [hi8_val]
      exact tail_step output a i.val ha_later h_tail
    have h_bounds' : ∀ j < 2 * i8.val, (0 : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val ≤ 15 := by
      rw [hi8_val]
      apply bounds_step output a i.val i4 i7
      · have hbot := hi2_le  -- i2.val ≤ 15
        push_cast [h_hi4]
        grind
      · have hbot := hi2_le
        push_cast [h_hi4]
        grind
      · have htop := hi5_le  -- i5.val ≤ 15
        push_cast [h_hi7]
        grind
      · have htop := hi5_le
        push_cast [h_hi7]
        grind
      · exact ha_even
      · exact ha_odd
      · exact ha_pref
      · exact h_bounds
    exact as_radix_16_loop0_spec self a i8 (by omega) h_inv' h_tail' h_bounds'
  case isFalse hge =>
    have hi_eq : i.val = 32 := by grind
    rw [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · unfold I8x64_as_Radix16 U8x32_as_Nat
      rw [hi_eq] at h_inv
      rw [← h_inv]
    · intro k hk
      exact h_bounds k (by omega)
  termination_by 32 - i.val
  decreasing_by
    simp only [hi8_val]
    omega

/-! ## Loop 1 -/

private lemma carry_zero_or_one (d : ℤ) (hlo : 0 ≤ d) (hhi : d ≤ 16) :
    (d + 8) / 16 = 0 ∨ (d + 8) / 16 = 1 := by
  omega

private lemma recenter_in_range (d : ℤ) :
    -8 ≤ d - (d + 8) / 16 * 16 ∧ d - (d + 8) / 16 * 16 ≤ 7 := by
  omega

private lemma next_digit_bounded (d' carry : ℤ)
    (hd_lo : 0 ≤ d') (hd_hi : d' ≤ 15)
    (hc : carry = 0 ∨ carry = 1) :
    0 ≤ d' + carry ∧ d' + carry ≤ 16 := by
  omega

/-- For `0 ≤ i ≤ 24`, `i >>> 4` succeeds and returns `i / 16`, which is `0` or `1`. -/
@[step]
private theorem i8_shiftRight_4_spec (i : I8) (h_lo : 0 ≤ i.val) (h_hi : i.val ≤ 24) :
    i >>> 4#i32 ⦃ (r : I8) =>
      r.val = i.val / 16 ∧
      0 ≤ r.val ∧
      r.val ≤ 1        ⦄ := by
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar,
             IScalar.shiftRight, IScalar.toNat, IScalar.val]
  norm_num
  simp only [IScalarTy.I32_numBits_eq, BitVec.reduceToInt, Nat.ofNat_nonneg, ↓reduceIte,
    Int.reduceLT, IScalarTy.I8_numBits_eq, Int.reduceToNat, spec_ok]
  have h : (i.bv.sshiftRight 4).toInt = i.val / 16 := by
    rw [BitVec.sshiftRight_eq]
    erw [BitVec.toInt_ofInt]
    change (i.val >>> (4 : Nat)).bmod (2 ^ 8) = i.val / 16
    rw [show i.val >>> (4 : Nat) = i.val / 16 by rw [Int.shiftRight_eq_div_pow]; norm_num]
    exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 7 (i.val / 16)
      (by norm_num; omega) (by norm_num; omega)
  simp only [IScalar.val] at h_lo h_hi h ⊢
  refine ⟨h, ?_, ?_⟩ <;> erw [h] <;> omega

/-- For `-8 ≤ i ≤ 7`, `i <<< 4` succeeds and returns `16 i`. -/
@[step]
private theorem i8_shiftLeft_4_spec (i : I8)
    (h_lo : -8 ≤ i.val) (h_hi : i.val ≤ 7) :
    i <<< 4#i32 ⦃ (r : I8) =>
      r.val = i.val * 16 ⦄ := by
  simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_IScalar, IScalar.shiftLeft,
             IScalar.toNat, IScalar.val]
  norm_num
  simp only [IScalarTy.I32_numBits_eq, BitVec.reduceToInt,
    Nat.ofNat_nonneg, ↓reduceIte, Int.reduceLT,
    IScalarTy.I8_numBits_eq, Int.reduceToNat, spec_ok]
  simp only [HShiftLeft.hShiftLeft]
  have hbv : (i.bv.shiftLeft 4 : BitVec 8) = i.bv * (16 : BitVec 8) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]
  change (i.bv.shiftLeft 4).toInt = (↑i : ℤ) * 16
  rw [hbv]
  simp only [IScalar.val]
  rw [BitVec.toInt_mul, show (16 : BitVec 8).toInt = 16 from by decide, I8.bv_toInt_eq]
  exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 7 (i.val * 16)
    (by norm_num; omega) (by norm_num; omega)

private lemma inv_step_loop1
    (output a : Array I8 64#usize) (i : ℕ) (hi : i < 63)
    (V : ℤ)
    (carry : ℤ)
    (ha_curr : (a[i]!).val = (output[i]!).val - carry * 16)
    (ha_next : (a[i + 1]!).val = (output[i + 1]!).val + carry)
    (ha_other : ∀ j, j ≠ i → j ≠ i + 1 → (a[j]! : I8).val = (output[j]!).val)
    (h_val : I8x64_as_Radix16 output = V) :
    I8x64_as_Radix16 a = V := by
  unfold I8x64_as_Radix16 at *
  rw [← h_val]
  have key : ∀ j ∈ Finset.range 64,
      (16 : ℤ)^j * (a[j]!).val =
      (16 : ℤ)^j * (output[j]!).val +
      (if j = i then -(carry * 16) * (16 : ℤ)^j else 0) +
      (if j = i + 1 then carry * (16 : ℤ)^j else 0) := by
    intro j _
    by_cases h1 : j = i
    · subst h1
      simp only [show j ≠ j + 1 from by omega, ite_false, add_zero]
      simp only [if_true]
      rw [ha_curr]; ring
    · by_cases h2 : j = i + 1
      · subst h2
        simp only [show i + 1 ≠ i from by omega, ite_false, if_true]
        linear_combination (16 : ℤ) ^ (i + 1) * ha_next
      · simp only [if_neg h1, if_neg h2, add_zero]
        linear_combination (16 : ℤ)^j * ha_other j h1 h2
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hi64  : i ∈ Finset.range 64     := Finset.mem_range.mpr (by omega)
  have hi164 : i + 1 ∈ Finset.range 64 := Finset.mem_range.mpr (by omega)
  rw [if_pos hi64, if_pos hi164]
  linarith [show -(carry * 16) * (16 : ℤ)^i + carry * (16 : ℤ)^(i + 1) = 0 from by ring]

private lemma tail_step_loop1
    (output a : Array I8 64#usize) (i : ℕ)
    (ha_other : ∀ j, j ≠ i → j ≠ i + 1 → (a[j]! : I8).val = (output[j]!).val)
    (h_tail : ∀ j, i < j → j < 64 →
        0 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    ∀ j, i + 1 < j → j < 64 →
        0 ≤ (a[j]! : I8).val ∧ (a[j]! : I8).val ≤ 15 := by
  intro j hj1 hj2
  rw [ha_other j (by omega) (by omega)]
  exact h_tail j (by omega) hj2

private lemma lo_bounds_prefix_step
    (output a : Array I8 64#usize) (i : ℕ)
    (i4 : I8)
    (hi4_lo : -8 ≤ (i4 : I8).val) (hi4_hi : (i4 : I8).val ≤ 7)
    (ha_curr : a[i]! = i4)
    (ha_other : ∀ j, j ≠ i → j ≠ i + 1 → (a[j]! : I8).val = (output[j]!).val)
    (h_lo : ∀ j < i,
        -8 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val < 8) :
    ∀ j < i + 1, -8 ≤ (a[j]!).val ∧ (a[j]!).val < 8 := by
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
  · rw [ha_other j (by omega) (by omega)]
    exact h_lo j hjlt
  · rw [ha_curr]
    exact ⟨hi4_lo, by omega⟩

/-- Loop 1 from index `i ≤ 63`. If the array has value `V`, the digits below `i` are in `[-8, 8)`,
digit `i` is in `[0, 16]` and the digits above `i` are in `[0, 15]`, then the loop succeeds and
returns an array of value `V` whose digits below `63` are in `[-8, 8)` and whose digit `63` is in
`[0, 16]`. -/
@[step]
theorem as_radix_16_loop1_spec
    (output : Array I8 64#usize)
    (i : Usize)
    (V : ℤ)
    (hi : i.val ≤ 63)
    (h_val : I8x64_as_Radix16 output = V)
    (h_lo : ∀ j < i.val,
        -8 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val < 8)
    (h_curr : 0 ≤ (output[i.val]! : I8).val ∧
              (output[i.val]! : I8).val ≤ 16)
    (h_tail : ∀ j, i.val < j → j < 64 →
        0 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    as_radix_16_loop1 output i ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = V ∧
      (∀ j < 63, -8 ≤ (result[j]!).val ∧ (result[j]!).val < 8) ∧
      0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16 ⦄ := by
  unfold as_radix_16_loop1
  split
  case isTrue hlt =>
    have hi' : i.val < 63 := by scalar_tac
    have h_i_lt : i.val < 64 := by omega
    step as ⟨i1, hi1⟩
    have h_i1_val : i1.val = (output[i.val]!).val := by
      rw [hi1, Array.getElem!_Nat_eq, getElem!_pos _ _ (by simpa using h_i_lt)]
    have h_i1_lo : 0 ≤ i1.val := by rw [h_i1_val]; exact h_curr.1
    have h_i1_hi : i1.val ≤ 16   := by rw [h_i1_val]; exact h_curr.2
    step as ⟨i2, hi2⟩
    step with i8_shiftRight_4_spec i2
      (by simp_all; omega) (by simp_all; omega) as ⟨carry, hcarry⟩
    have h_carry_val : carry.val = (i1.val + 8) / 16 := by
      simp[hcarry,hi2]
    have h_carry_01 : carry.val = 0 ∨ carry.val = 1 := by
      have h := carry_zero_or_one i1.val h_i1_lo h_i1_hi
      omega
    step with i8_shiftLeft_4_spec carry (by omega) (by omega) as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨output1, h_upd1⟩
    step as ⟨i5, hi5⟩
    have hi5_val : i5.val = i.val + 1 := by scalar_tac
    have h_i5_lt : i5.val < 64 := by omega
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    case hmax =>
      have hne : i5.val ≠ i.val := by omega
      have h6 := h_upd1 i5.val hne
      have hb := h_tail i5.val (by omega) (by omega)
      have hi6v : i6.val = (output1[i5.val]!).val := by
        rw [hi6, Array.getElem!_Nat_eq, getElem!_pos _ _ (by simpa using h_i5_lt)]
      rw [hi6v, h6]
      have hcle : carry.val ≤ 1 := by rcases h_carry_01 with hc | hc <;> omega
      scalar_tac
    step as ⟨a, h_upd2⟩
    have h_i4_val : i4.val = i1.val - carry.val * 16 := by
      simp_all
    have h_i7_val : i7.val = (output[i.val + 1]!).val + carry.val := by
      have hi6v : i6.val = (output1[i5.val]!).val := by
        rw [hi6, Array.getElem!_Nat_eq, getElem!_pos _ _ (by simpa using h_i5_lt)]
      rw [hi7, hi6v, h_upd1 i5.val (by omega), hi5_val]
    have ha_curr_eq : a[i.val]! = i4 := by
      have hne : i5.val ≠ i.val := by omega
      have h2 := h_upd2 i.val (by rw [hi5_val]; omega)
      simp only [h2]
      simp_all
    have ha_next_eq : a[i.val + 1]! = i7 := by
      rw [← hi5_val]
      simp_all
    have ha_other : ∀ j, j ≠ i.val → j ≠ i.val + 1 →
        (a[j]! : I8).val = (output[j]!).val := by
      intro j hj1 hj2
      have eq2 := h_upd2 j (by rw [hi5_val]; exact hj2)
      simp only [eq2]
      have eq1 := h_upd1 j hj1
      simp only [eq1]
    have h_val' : I8x64_as_Radix16 a = V := by
      apply inv_step_loop1 output a i.val hi' V carry
      · rw [ha_curr_eq, h_i4_val, h_i1_val]
      · rw [ha_next_eq, h_i7_val]
      · intro j hj1 hj2; exact ha_other j hj1 hj2
      · exact h_val
    have h_i4_rng := recenter_in_range i1.val
    have h_i4_lo : -8 ≤ i4.val := by
      rw [h_i4_val, h_carry_val]; linarith [h_i4_rng.1]
    have h_i4_hi : i4.val ≤ 7 := by
      rw [h_i4_val, h_carry_val]; linarith [h_i4_rng.2]
    have h_lo' : ∀ j < i5.val, -8 ≤ (a[j]!).val ∧ (a[j]!).val < 8 := by
      rw [hi5_val]
      apply lo_bounds_prefix_step output a i.val i4 h_i4_lo h_i4_hi ha_curr_eq
      · intro j hj1 hj2
        exact ha_other j hj1 (by rw [← hi5_val]; simp_all)
      · exact h_lo
    have h_curr' : 0 ≤ (a[i5.val]!).val ∧ (a[i5.val]!).val ≤ 16 := by
      rw [hi5_val, ha_next_eq, h_i7_val]
      have h_next := h_tail (i.val + 1) (by omega) (by omega)
      exact next_digit_bounded (output[i.val + 1]!).val carry.val
        h_next.1 h_next.2 h_carry_01
    have h_tail' : ∀ j, i5.val < j → j < 64 →
        0 ≤ (a[j]!).val ∧ (a[j]!).val ≤ 15 := by
      rw [hi5_val]
      apply tail_step_loop1 output a i.val
      · intro j hj1 hj2
        exact ha_other j hj1 (by rw [← hi5_val]; simp_all)
      · exact h_tail
    exact as_radix_16_loop1_spec a i5 V (by omega)
      h_val' h_lo' h_curr' h_tail'
  case isFalse hge =>
    have hi_eq : i.val = 63 := by scalar_tac
    rw [WP.spec_ok]
    refine ⟨h_val, ?_, ?_⟩
    · intro j hj
      exact h_lo j (by omega)
    · rw [hi_eq] at h_curr
      exact ⟨h_curr.1, h_curr.2⟩
  termination_by 63 - i.val
  decreasing_by
    simp only [hi5_val]
    omega

/-! ## The spec -/

/-- If byte 31 is at most `127`, the scalar is less than `2^255`. -/
private lemma U8x32_as_Nat_lt_pow255 (self : Scalar)
    (h_top : (self.bytes[31]!).val ≤ 127) :
    U8x32_as_Nat self.bytes < 2 ^ 255 := by
  simp only [U8x32_as_Nat]
  have key : ∀ k, k ≤ 32 →
      ∑ i ∈ Finset.range k, 2 ^ (8 * i) * (self.bytes[i]!).val < 2 ^ (8 * k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hbnd : (self.bytes[k]!).val < 256 := by
        have := (self.bytes[k]!).hBounds; scalar_tac
      have ih' := ih (by omega)
      have h8k : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
        rw [show 8 * (k + 1) = 8 * k + 8 from by ring, pow_add]; norm_num
      nlinarith [Nat.two_pow_pos (8 * k)]
  have h31 : ∑ i ∈ Finset.range 31, 2 ^ (8 * i) * (self.bytes[i]!).val < 2 ^ (8 * 31) :=
    key 31 (by omega)
  have hsplit : ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (self.bytes[i]!).val =
      ∑ i ∈ Finset.range 31, 2 ^ (8 * i) * (self.bytes[i]!).val +
      2 ^ (8 * 31) * (self.bytes[31]!).val :=
    Finset.sum_range_succ (fun i => 2 ^ (8 * i) * (self.bytes[i]!).val) 31
  rw [hsplit]
  nlinarith [show (2 : ℕ) ^ (8 * 31) * 128 = 2 ^ 255 from by norm_num,
             Nat.mul_le_mul_left (2 ^ (8 * 31)) h_top]

/-- If the digits `d` have value `V < 2^255` and `-8 ≤ d_i` for `i < 63`, then `d_63 ≤ 8`, because
`d_63 · 16^63 = V - ∑ i < 63, 16^i · d_i < 8 · 16^63 + 8 · (16^63 - 1) / 15`. -/
private lemma digit_63_le_8
    (digits : Array I8 64#usize)
    (V : ℕ)
    (h_val : I8x64_as_Radix16 digits = (V : ℤ))
    (h_V_lt : V < 2 ^ 255)
    (h_inner : ∀ i < 63, -8 ≤ (digits[i]!).val ∧ (digits[i]!).val < 8) :
    (digits[63]!).val ≤ 8 := by
  by_contra h_neg
  push Not at h_neg
  have h_s63_ge_9 : 9 ≤ (digits[63]!).val := h_neg
  -- Split the full sum: s_63 * 16^63 + ∑_{i<63} 16^i * s_i = V.
  have h_split : (digits[63]!).val * (16 : ℤ) ^ 63 +
      ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i * (digits[i]!).val = V := by
    rw [← h_val]
    unfold I8x64_as_Radix16
    rw [Finset.sum_range_succ (fun i => (16 : ℤ) ^ i * (digits[i]!).val) 63]
    ring
  -- Lower bound the inner signed sum by -8 * ∑_{i<63} 16^i.
  have h_inner_lb :
      -8 * ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i ≤
        ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i * (digits[i]!).val := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intros i hi
    have hi63 : i < 63 := Finset.mem_range.mp hi
    have h_pow : (0 : ℤ) ≤ (16 : ℤ) ^ i := pow_nonneg (by norm_num) i
    have := (h_inner i hi63).1
    nlinarith
  -- Geometric sum: (∑_{i<63} 16^i) * (16 - 1) = 16^63 - 1.
  have h_geom : 15 * ∑ i ∈ Finset.range 63, (16 : ℤ) ^ i = (16 : ℤ) ^ 63 - 1 := by
    have := geom_sum_mul (16 : ℤ) 63
    linarith
  -- 2^255 = 8 * 16^63.
  have h_255_eq : (2 : ℤ) ^ 255 = 8 * (16 : ℤ) ^ 63 := by
    rw [show (255 : ℕ) = 3 + 4 * 63 from by norm_num, pow_add, pow_mul]
    norm_num
  have h_V_Z : (V : ℤ) < (2 : ℤ) ^ 255 := by exact_mod_cast h_V_lt
  have h_pow_pos : (0 : ℤ) < (16 : ℤ) ^ 63 := pow_pos (by norm_num) 63
  -- Derive contradiction: if s_63 ≥ 9, then 9 * 16^63 ≤ s_63 * 16^63 = V - inner_sum ≤ V + 8 * S,
  -- giving 135 * 16^63 ≤ 15V + 8(16^63 - 1) < 120 * 16^63 + 8 * 16^63 = 128 * 16^63. Contradiction.
  nlinarith [h_split, h_inner_lb, h_geom, h_V_Z, h_255_eq, h_pow_pos, h_s63_ge_9,
             mul_pos (show (0:ℤ) < 9 from by norm_num) h_pow_pos]

/-- `as_radix_16_spec` with the bound `d_63 ≤ 16` of loop 1. -/
private theorem as_radix_16_spec_le_16 (self : Scalar)
    (h_top : (self.bytes[31]!).val ≤ 127) :
    as_radix_16 self ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes) ∧
      (∀ i < 63, -8 ≤ (result[i]!).val ∧ (result[i]!).val < 8) ∧
      0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16 ⦄ := by
  simp only [as_radix_16]
  unfold scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8.index
  step as ⟨i1, hi1⟩
  step*
  · subst hi1
    have hb := h_top
    rw [Array.getElem!_Nat_eq, getElem!_pos _ _ (by scalar_tac)] at hb
    scalar_tac
  · simp
  · intro j _ hj
    simp only [Array.getElem!_Nat_eq, Array.repeat_val]
    rw [List.getElem!_replicate] <;> first | rfl | scalar_tac

/-- If `self.bytes[31] ≤ 127`, then `as_radix_16 self` succeeds and returns digits `d` with
`I8x64_as_Radix16 d = U8x32_as_Nat self.bytes`, `-8 ≤ d_i < 8` for `i < 63` and
`0 ≤ d_63 ≤ 8`. -/
@[step]
theorem as_radix_16_spec (self : Scalar) (h_top : (self.bytes[31]!).val ≤ 127) :
    as_radix_16 self ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes) ∧
      (∀ i < 63, -8 ≤ (result[i]!).val ∧ (result[i]!).val < 8) ∧
      0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 8 ⦄ := by
  apply spec_mono (as_radix_16_spec_le_16 self h_top)
  rintro r ⟨hv, hi, h0, -⟩
  exact ⟨hv, hi, h0, digit_63_le_8 r _ hv (U8x32_as_Nat_lt_pow255 self h_top) hi⟩

/--
info: 'curve25519_dalek.scalar.Scalar.as_radix_16_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms as_radix_16_spec

end curve25519_dalek.scalar.Scalar
