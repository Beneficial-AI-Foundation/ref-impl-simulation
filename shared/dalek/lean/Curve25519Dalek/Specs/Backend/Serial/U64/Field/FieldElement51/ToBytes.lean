/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::to_bytes`

This function converts a field element to its canonical 32-byte little-endian representation.
It performs reduction modulo `2 ^ 255 - 19` and encodes the result as bytes.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"

Port note (ref-impl-simulation, Aeneas d119a474): the helper lemmas up to
`canonical_reduction_mod_p` are kept, but the ten `bv_decide` proofs are replaced by `omega`
and `Nat` bit lemmas (`or_shift_mod`, `decompose_or_shift`), because `bv_decide` adds
native-code axioms. The proof of `to_bytes_spec` is new. Upstream steps through all of
`to_bytes` at once with `maxHeartbeats 1600000`. Here `to_bytes_unfold` splits it into
`to_bytes_q`, `to_bytes_carry` and `to_bytes_pack`, and `to_bytes_pack_unfold` splits the
packing into five parts, one per limb boundary. Each part has its own spec. The statement of
`to_bytes_spec` did not change.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

set_option linter.unusedSimpArgs false

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
## TODO
- move general helpers lemmas to a more central location
- move to standard library the following:
  attribute [simp_scalar_simps] BitVec.toNat_shiftLeft
-/

attribute [simp_scalar] BitVec.toNat_shiftLeft

@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]

-- This is specific to the problem below
theorem recompose_decomposed_limb (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val =
  limb.val % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 8 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8)
  := by
  simp only [Nat.shiftRight_eq_div_pow]
  omega


-- Byte reconstruction for split limbs at each boundary.
-- Boundary byte k uses (limb_lo >>> hi_shift ||| limb_hi <<< lo_shift).
-- The 4 boundaries have lo_shifts: 3, 6, 1, 4.

theorem recompose_decomposed_limb_shift3 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 3 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 5 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 13 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 21 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 29 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 37 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 45 % 2 ^ 8) =
  2 ^ 3 * limb.val := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem recompose_decomposed_limb_shift6 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 6 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 2 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 10 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 18 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 26 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 34 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 42 % 2 ^ 8)
  + 2 ^ 56 * (limb.val >>> 50 % 2 ^ 8) =
  2 ^ 6 * limb.val := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem recompose_decomposed_limb_shift1 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 1 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 7 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 15 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 23 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 31 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 39 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 47 % 2 ^ 8) =
  2 ^ 1 * limb.val := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem recompose_decomposed_limb_shift4 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 4 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 4 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8) =
  2 ^ 4 * limb.val := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- Two values with disjoint bits: `x < 2 ^ s` and a multiple of `2 ^ s`. -/
theorem or_shift_mod (x c s : ℕ) (hs : s ≤ 8) (hx : x < 2 ^ s) :
    (x ||| 2 ^ s * c) % 2 ^ 8 = x % 2 ^ 8 + (2 ^ s * c) % 2 ^ 8 := by
  rw [Nat.lor_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  interval_cases s <;> simp at hx ⊢ <;> omega

/-- A boundary byte: the top bits of one limb OR the bottom bits of the next. -/
theorem decompose_or_shift (a b k s : ℕ) (hs : s ≤ 8) (hks : k + s = 51) (ha : a < 2 ^ 51) :
    ((a >>> k ||| b <<< s % U64.size) % 2 ^ 8) = (a >>> k % 2 ^ 8) + ((b <<< s) % 2 ^ 8) := by
  have hx : a >>> k < 2 ^ s := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.add_comm, hks]; exact ha
  have hsz : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
  have hdvd : 2 ^ s ∣ b <<< s % U64.size := by
    rw [Nat.dvd_mod_iff (by rw [hsz]; exact pow_dvd_pow 2 (by omega)), Nat.shiftLeft_eq]
    exact Dvd.intro_left _ rfl
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, or_shift_mod _ c s hs hx, ← hc,
    Nat.mod_mod_of_dvd _ (by rw [hsz]; exact pow_dvd_pow 2 (by omega))]

-- OR decomposition at boundary bytes: the shifted halves occupy disjoint bit ranges.
-- One lemma per boundary shift.
theorem decompose_or_limbs_shift3 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 3 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) + ((limb1.val <<< 3) % 2 ^ 8) := by
  exact decompose_or_shift _ _ 48 3 (by norm_num) (by norm_num) h

theorem decompose_or_limbs_shift6 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 45 ||| limb1.val <<< 6 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 45 % 2 ^ 8) + ((limb1.val <<< 6) % 2 ^ 8) := by
  exact decompose_or_shift _ _ 45 6 (by norm_num) (by norm_num) h

theorem decompose_or_limbs_shift1 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 50 ||| limb1.val <<< 1 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 50 % 2 ^ 8) + ((limb1.val <<< 1) % 2 ^ 8) := by
  exact decompose_or_shift _ _ 50 1 (by norm_num) (by norm_num) h

theorem decompose_or_limbs_shift4 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 47 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 47 % 2 ^ 8) + ((limb1.val <<< 4) % 2 ^ 8) := by
  exact decompose_or_shift _ _ 47 4 (by norm_num) (by norm_num) h

/-- Byte-by-byte packing formula for 5 × 51-bit limbs into 32 LE bytes.
    Matches the Rust source (field.rs:419-452) and the Lean extraction.
    The 4 boundary bytes (6, 12, 19, 25) combine bits from adjacent limbs.

    NOTE: This describes the byte packing of CANONICALIZED limbs (each < 2^51).
    The full `to_bytes` function first reduces and canonicalizes before packing. -/
def bytes_match_limbs (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  -- Limb 0 (bits 0-50) → bytes 0-6
  s.val[0]!.val = L.val[0]!.val % 2^8 ∧
  s.val[1]!.val = L.val[0]!.val >>> 8 % 2^8 ∧
  s.val[2]!.val = L.val[0]!.val >>> 16 % 2^8 ∧
  s.val[3]!.val = L.val[0]!.val >>> 24 % 2^8 ∧
  s.val[4]!.val = L.val[0]!.val >>> 32 % 2^8 ∧
  s.val[5]!.val = L.val[0]!.val >>> 40 % 2^8 ∧
  s.val[6]!.val = (L.val[0]!.val >>> 48 ||| L.val[1]!.val <<< 3 % U64.size) % 2^8 ∧
  -- Limb 1 (bits 51-101) → bytes 7-12
  s.val[7]!.val = L.val[1]!.val >>> 5 % 2^8 ∧
  s.val[8]!.val = L.val[1]!.val >>> 13 % 2^8 ∧
  s.val[9]!.val = L.val[1]!.val >>> 21 % 2^8 ∧
  s.val[10]!.val = L.val[1]!.val >>> 29 % 2^8 ∧
  s.val[11]!.val = L.val[1]!.val >>> 37 % 2^8 ∧
  s.val[12]!.val = (L.val[1]!.val >>> 45 ||| L.val[2]!.val <<< 6 % U64.size) % 2^8 ∧
  -- Limb 2 (bits 102-152) → bytes 13-19
  s.val[13]!.val = L.val[2]!.val >>> 2 % 2^8 ∧
  s.val[14]!.val = L.val[2]!.val >>> 10 % 2^8 ∧
  s.val[15]!.val = L.val[2]!.val >>> 18 % 2^8 ∧
  s.val[16]!.val = L.val[2]!.val >>> 26 % 2^8 ∧
  s.val[17]!.val = L.val[2]!.val >>> 34 % 2^8 ∧
  s.val[18]!.val = L.val[2]!.val >>> 42 % 2^8 ∧
  s.val[19]!.val = (L.val[2]!.val >>> 50 ||| L.val[3]!.val <<< 1 % U64.size) % 2^8 ∧
  -- Limb 3 (bits 153-203) → bytes 20-25
  s.val[20]!.val = L.val[3]!.val >>> 7 % 2^8 ∧
  s.val[21]!.val = L.val[3]!.val >>> 15 % 2^8 ∧
  s.val[22]!.val = L.val[3]!.val >>> 23 % 2^8 ∧
  s.val[23]!.val = L.val[3]!.val >>> 31 % 2^8 ∧
  s.val[24]!.val = L.val[3]!.val >>> 39 % 2^8 ∧
  s.val[25]!.val = (L.val[3]!.val >>> 47 ||| L.val[4]!.val <<< 4 % U64.size) % 2^8 ∧
  -- Limb 4 (bits 204-254) → bytes 26-31
  s.val[26]!.val = L.val[4]!.val >>> 4 % 2^8 ∧
  s.val[27]!.val = L.val[4]!.val >>> 12 % 2^8 ∧
  s.val[28]!.val = L.val[4]!.val >>> 20 % 2^8 ∧
  s.val[29]!.val = L.val[4]!.val >>> 28 % 2^8 ∧
  s.val[30]!.val = L.val[4]!.val >>> 36 % 2^8 ∧
  s.val[31]!.val = L.val[4]!.val >>> 44 % 2^8


/-- Byte packing correctness: when all limbs < 2^51 and bytes match the packing formula,
    the little-endian byte interpretation equals the radix-2^51 limb interpretation. -/
theorem byte_packing_eq (L : Array U64 5#usize) (s : Array U8 32#usize)
    (hL : ∀ i < 5, (L.val[i]! : U64).val < 2 ^ 51)
    (hbytes : bytes_match_limbs L s) :
    U8x32_as_Nat s = Field51_as_Nat L := by
  unfold bytes_match_limbs at hbytes
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
          hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
          hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31⟩ := hbytes
  have hL0 : (L.val[0]! : U64).val < 2 ^ 51 := hL 0 (by omega)
  have hL1 : (L.val[1]! : U64).val < 2 ^ 51 := hL 1 (by omega)
  have hL2 : (L.val[2]! : U64).val < 2 ^ 51 := hL 2 (by omega)
  have hL3 : (L.val[3]! : U64).val < 2 ^ 51 := hL 3 (by omega)
  have hL4 : (L.val[4]! : U64).val < 2 ^ 51 := hL 4 (by omega)
  have hd6 := decompose_or_limbs_shift3 L.val[0]! L.val[1]! hL0
  have hd12 := decompose_or_limbs_shift6 L.val[1]! L.val[2]! hL1
  have hd19 := decompose_or_limbs_shift1 L.val[2]! L.val[3]! hL2
  have hd25 := decompose_or_limbs_shift4 L.val[3]! L.val[4]! hL3
  have hr0 := recompose_decomposed_limb L.val[0]! hL0
  have hr1 := recompose_decomposed_limb_shift3 L.val[1]! hL1
  have hr2 := recompose_decomposed_limb_shift6 L.val[2]! hL2
  have hr3 := recompose_decomposed_limb_shift1 L.val[3]! hL3
  have hr4 := recompose_decomposed_limb_shift4 L.val[4]! hL4
  unfold U8x32_as_Nat Field51_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Array.getElem!_Nat_eq, Nat.reduceMul,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
    hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
    hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31,
    hd6, hd12, hd19, hd25]
  linarith

/-- For a U8 value < 128, AND with 128 is 0 (bit 7 is clear). -/
private lemma u8_and_128_eq_zero_of_lt (x : U8) (h : x.val < 128) :
    (x &&& 128#u8).val = 0 := by
  rw [UScalar.val_and]
  have : (128#u8 : U8).val = 2 ^ 7 := by simp
  rw [this, Nat.and_two_pow, Nat.testBit_lt_two_pow (by simpa using h)]
  simp

/-- Canonical reduction: the q-computation + conditional subtraction + carry chain
    produces a value that is congruent mod p and canonical (< p).

    The algorithm computes q = ⌊(F + 19) / 2^255⌋ ∈ {0,1}, then adds 19*q to limb 0
    and carry-propagates with masking to 51 bits. The result satisfies:
    - Field51_as_Nat(output) ≡ Field51_as_Nat(input) [MOD p]
    - Field51_as_Nat(output) < p
    - output limbs = carry-propagate(input + 19*q) masked to 51 bits

    Often when this lemma is applied f0,...,f4 are bounded by 2 ^ 52, but it's not needed for the
    proof. The hypothesis hF stems from the fact that the lemma will be applied to the output of
    reduce_spec

    Ported from Verus `lemma_to_bytes_reduction` in dalek-lite. -/
private lemma canonical_reduction_mod_p
    (f0 f1 f2 f3 f4 : ℕ)
    (hF : f0 + 2 ^ 51 * f1 + 2 ^ 102 * f2 + 2 ^ 153 * f3 + 2 ^ 204 * f4 < 2 * (2 ^ 255 - 19))
    (q : ℕ)
    (hq : q = (((((f0 + 19) / 2 ^ 51 + f1) / 2 ^ 51 + f2) / 2 ^ 51 + f3) / 2 ^ 51 + f4) / 2 ^ 51)
    (l0 l1 l2 l3 l4 : ℕ)
    (hl0 : l0 = (f0 + 19 * q) % 2 ^ 51)
    (hl1 : l1 = (f1 + (f0 + 19 * q) / 2 ^ 51) % 2 ^ 51)
    (hl2 : l2 = (f2 + (f1 + (f0 + 19 * q) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hl3 : l3 = (f3 + (f2 + (f1 + (f0 + 19 * q) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hl4 : l4 =
      (f4 + (f3 + (f2 + (f1 + (f0 + 19 * q) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51) :
    (l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4) % (2 ^ 255 - 19) =
      (f0 + 2 ^ 51 * f1 + 2 ^ 102 * f2 + 2 ^ 153 * f3 + 2 ^ 204 * f4) % (2 ^ 255 - 19) ∧
    l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 < 2 ^ 255 - 19 := by
  -- Abbreviate F
  set F := f0 + 2 ^ 51 * f1 + 2 ^ 102 * f2 + 2 ^ 153 * f3 + 2 ^ 204 * f4 with hF_def
  -- === Q-chain: carry variables for the (F+19) computation that determines q ===
  -- (operand order: carry + fi, matching the nesting in hq)
  set d0 := (f0 + 19) / 2 ^ 51
  set d1 := (d0 + f1) / 2 ^ 51
  set d2 := (d1 + f2) / 2 ^ 51
  set d3 := (d2 + f3) / 2 ^ 51
  -- After set, hq simplifies to: q = (d3 + f4) / 2^51
  -- Q-chain telescoping steps (each is just Nat.mod_add_div)
  have hqt0 : (f0 + 19) % 2 ^ 51 + d0 * 2 ^ 51 = f0 + 19 := by omega
  have hqt1 : (d0 + f1) % 2 ^ 51 + d1 * 2 ^ 51 = d0 + f1 := by omega
  have hqt2 : (d1 + f2) % 2 ^ 51 + d2 * 2 ^ 51 = d1 + f2 := by omega
  have hqt3 : (d2 + f3) % 2 ^ 51 + d3 * 2 ^ 51 = d2 + f3 := by omega
  have hqt4 : (d3 + f4) % 2 ^ 51 + q * 2 ^ 51 = d3 + f4 := by rw [hq]; omega
  -- Q-chain: limbs of (F+19) are each < 2^51
  have hqm0 := Nat.mod_lt (f0 + 19) (show 0 < 2 ^ 51 by norm_num)
  have hqm1 := Nat.mod_lt (d0 + f1) (show 0 < 2 ^ 51 by norm_num)
  have hqm2 := Nat.mod_lt (d1 + f2) (show 0 < 2 ^ 51 by norm_num)
  have hqm3 := Nat.mod_lt (d2 + f3) (show 0 < 2 ^ 51 by norm_num)
  have hqm4 := Nat.mod_lt (d3 + f4) (show 0 < 2 ^ 51 by norm_num)
  -- Q-chain telescoping: Lq + q * 2^255 = F + 19 (where Lq < 2^255)
  have hqtel : (f0 + 19) % 2 ^ 51 + 2 ^ 51 * ((d0 + f1) % 2 ^ 51) +
      2 ^ 102 * ((d1 + f2) % 2 ^ 51) + 2 ^ 153 * ((d2 + f3) % 2 ^ 51) +
      2 ^ 204 * ((d3 + f4) % 2 ^ 51) + q * 2 ^ 255 = F + 19 := by omega
  -- q ≤ 1 (from Lq + q*2^255 = F+19, Lq ≥ 0, F < 2p < 2^256)
  have hqle : q ≤ 1 := by omega
  -- === Main chain: carry variables for the (F + 19*q) reduction ===
  -- (operand order: fi + carry, matching the nesting in hl0..hl4)
  set c0 := (f0 + 19 * q) / 2 ^ 51
  set c1 := (f1 + c0) / 2 ^ 51
  set c2 := (f2 + c1) / 2 ^ 51
  set c3 := (f3 + c2) / 2 ^ 51
  set c4 := (f4 + c3) / 2 ^ 51
  -- Main chain telescoping: li + ci * 2^51 = si  (from Nat.mod_add_div)
  have ht0 : l0 + c0 * 2 ^ 51 = f0 + 19 * q := by
    rw [hl0, Nat.mul_comm c0]; exact Nat.mod_add_div _ _
  have ht1 : l1 + c1 * 2 ^ 51 = f1 + c0 := by
    rw [hl1, Nat.mul_comm c1]; exact Nat.mod_add_div _ _
  have ht2 : l2 + c2 * 2 ^ 51 = f2 + c1 := by
    rw [hl2, Nat.mul_comm c2]; exact Nat.mod_add_div _ _
  have ht3 : l3 + c3 * 2 ^ 51 = f3 + c2 := by
    rw [hl3, Nat.mul_comm c3]; exact Nat.mod_add_div _ _
  have ht4 : l4 + c4 * 2 ^ 51 = f4 + c3 := by
    rw [hl4, Nat.mul_comm c4]; exact Nat.mod_add_div _ _
  -- Main telescoping: L + c4 * 2^255 = F + 19*q
  have htel : l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 +
      c4 * 2 ^ 255 = F + 19 * q := by
    linear_combination ht0 + 2^51 * ht1 + 2^102 * ht2 + 2^153 * ht3 + 2^204 * ht4
  -- L < 2^255 (each limb < 2^51 from masking)
  have hl0b : l0 < 2 ^ 51 := by rw [hl0]; exact Nat.mod_lt _ (by norm_num)
  have hl1b : l1 < 2 ^ 51 := by rw [hl1]; exact Nat.mod_lt _ (by norm_num)
  have hl2b : l2 < 2 ^ 51 := by rw [hl2]; exact Nat.mod_lt _ (by norm_num)
  have hl3b : l3 < 2 ^ 51 := by rw [hl3]; exact Nat.mod_lt _ (by norm_num)
  have hl4b : l4 < 2 ^ 51 := by rw [hl4]; exact Nat.mod_lt _ (by norm_num)
  have hLb : l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 < 2 ^ 255 := by
    omega
  -- Case split on q
  interval_cases q
  · -- q = 0: q-chain gives F+19 = Lq < 2^255, so F < p. Main chain: c4=0, L=F.
    have hFp : F < 2 ^ 255 - 19 := by agrind
    have hc4 : c4 = 0 := by agrind
    constructor <;> agrind
  · -- q = 1: q-chain gives F+19 ≥ 2^255. Main chain: c4=1, L = F-p.
    have hFge : F + 19 ≥ 2 ^ 255 := by omega
    have hc4 : c4 = 1 := by omega
    constructor <;> omega

/-! ## Spec for `to_bytes`

The stages below are copies of parts of `to_bytes` (see the port note in the header).
`to_bytes_unfold` and `to_bytes_pack_unfold` prove that the parts compose to `to_bytes`. -/

/-- Stage 1 of `to_bytes`, copied from `Funs.lean`: the carry chain of `fe + 19` that gives
`q`. `to_bytes_unfold` proves that the stages compose to `to_bytes`. -/
def to_bytes_q (fe : FieldElement51) (i : U64) : Result U64 := do
  let i1 ← i + 19#u64
  let q ← i1 >>> 51#i32
  let i2 ← Array.index_usize fe 1#usize
  let i3 ← i2 + q
  let q1 ← i3 >>> 51#i32
  let i4 ← Array.index_usize fe 2#usize
  let i5 ← i4 + q1
  let q2 ← i5 >>> 51#i32
  let i6 ← Array.index_usize fe 3#usize
  let i7 ← i6 + q2
  let q3 ← i7 >>> 51#i32
  let i8 ← Array.index_usize fe 4#usize
  let i9 ← i8 + q3
  let q4 ← i9 >>> 51#i32
  ok q4

/-- Stage 2 of `to_bytes`, copied from `Funs.lean`: add `19 * q` and carry, masking each limb
to 51 bits. -/
def to_bytes_carry (fe : FieldElement51) (i q4 : U64) : Result FieldElement51 := do
  let i10 ← 19#u64 * q4
  let i11 ← i + i10
  let limbs ← Array.update fe 0#usize i11
  let i12 ← 1#u64 <<< 51#i32
  let low_51_bit_mask ← i12 - 1#u64
  let i13 ← Array.index_usize limbs 0#usize
  let i14 ← i13 >>> 51#i32
  let i15 ← Array.index_usize limbs 1#usize
  let i16 ← i15 + i14
  let limbs1 ← Array.update limbs 1#usize i16
  let i17 ← Array.index_usize limbs1 0#usize
  let i18 ← lift (i17 &&& low_51_bit_mask)
  let limbs2 ← Array.update limbs1 0#usize i18
  let i19 ← Array.index_usize limbs2 1#usize
  let i20 ← i19 >>> 51#i32
  let i21 ← Array.index_usize limbs2 2#usize
  let i22 ← i21 + i20
  let limbs3 ← Array.update limbs2 2#usize i22
  let i23 ← Array.index_usize limbs3 1#usize
  let i24 ← lift (i23 &&& low_51_bit_mask)
  let limbs4 ← Array.update limbs3 1#usize i24
  let i25 ← Array.index_usize limbs4 2#usize
  let i26 ← i25 >>> 51#i32
  let i27 ← Array.index_usize limbs4 3#usize
  let i28 ← i27 + i26
  let limbs5 ← Array.update limbs4 3#usize i28
  let i29 ← Array.index_usize limbs5 2#usize
  let i30 ← lift (i29 &&& low_51_bit_mask)
  let limbs6 ← Array.update limbs5 2#usize i30
  let i31 ← Array.index_usize limbs6 3#usize
  let i32 ← i31 >>> 51#i32
  let i33 ← Array.index_usize limbs6 4#usize
  let i34 ← i33 + i32
  let limbs7 ← Array.update limbs6 4#usize i34
  let i35 ← Array.index_usize limbs7 3#usize
  let i36 ← lift (i35 &&& low_51_bit_mask)
  let limbs8 ← Array.update limbs7 3#usize i36
  let i37 ← Array.index_usize limbs8 4#usize
  let i38 ← lift (i37 &&& low_51_bit_mask)
  let limbs9 ← Array.update limbs8 4#usize i38
  ok limbs9

/-- Stage 3 of `to_bytes`, copied from `Funs.lean`: pack five 51-bit limbs into 32 bytes.
`to_bytes_pack_unfold` splits it into `to_bytes_pack0` to `to_bytes_pack4`. -/
def to_bytes_pack (limbs9 : FieldElement51) : Result (Array U8 32#usize) := do
  let s := Array.repeat 32#usize 0#u8
  let i39 ← Array.index_usize limbs9 0#usize
  let i40 ← lift (UScalar.cast .U8 i39)
  let s1 ← Array.update s 0#usize i40
  let i41 ← i39 >>> 8#i32
  let i42 ← lift (UScalar.cast .U8 i41)
  let s2 ← Array.update s1 1#usize i42
  let i43 ← i39 >>> 16#i32
  let i44 ← lift (UScalar.cast .U8 i43)
  let s3 ← Array.update s2 2#usize i44
  let i45 ← i39 >>> 24#i32
  let i46 ← lift (UScalar.cast .U8 i45)
  let s4 ← Array.update s3 3#usize i46
  let i47 ← i39 >>> 32#i32
  let i48 ← lift (UScalar.cast .U8 i47)
  let s5 ← Array.update s4 4#usize i48
  let i49 ← i39 >>> 40#i32
  let i50 ← lift (UScalar.cast .U8 i49)
  let s6 ← Array.update s5 5#usize i50
  let i51 ← i39 >>> 48#i32
  let i52 ← Array.index_usize limbs9 1#usize
  let i53 ← i52 <<< 3#i32
  let i54 ← lift (i51 ||| i53)
  let i55 ← lift (UScalar.cast .U8 i54)
  let s7 ← Array.update s6 6#usize i55
  let i56 ← i52 >>> 5#i32
  let i57 ← lift (UScalar.cast .U8 i56)
  let s8 ← Array.update s7 7#usize i57
  let i58 ← i52 >>> 13#i32
  let i59 ← lift (UScalar.cast .U8 i58)
  let s9 ← Array.update s8 8#usize i59
  let i60 ← i52 >>> 21#i32
  let i61 ← lift (UScalar.cast .U8 i60)
  let s10 ← Array.update s9 9#usize i61
  let i62 ← i52 >>> 29#i32
  let i63 ← lift (UScalar.cast .U8 i62)
  let s11 ← Array.update s10 10#usize i63
  let i64 ← i52 >>> 37#i32
  let i65 ← lift (UScalar.cast .U8 i64)
  let s12 ← Array.update s11 11#usize i65
  let i66 ← i52 >>> 45#i32
  let i67 ← Array.index_usize limbs9 2#usize
  let i68 ← i67 <<< 6#i32
  let i69 ← lift (i66 ||| i68)
  let i70 ← lift (UScalar.cast .U8 i69)
  let s13 ← Array.update s12 12#usize i70
  let i71 ← i67 >>> 2#i32
  let i72 ← lift (UScalar.cast .U8 i71)
  let s14 ← Array.update s13 13#usize i72
  let i73 ← i67 >>> 10#i32
  let i74 ← lift (UScalar.cast .U8 i73)
  let s15 ← Array.update s14 14#usize i74
  let i75 ← i67 >>> 18#i32
  let i76 ← lift (UScalar.cast .U8 i75)
  let s16 ← Array.update s15 15#usize i76
  let i77 ← i67 >>> 26#i32
  let i78 ← lift (UScalar.cast .U8 i77)
  let s17 ← Array.update s16 16#usize i78
  let i79 ← i67 >>> 34#i32
  let i80 ← lift (UScalar.cast .U8 i79)
  let s18 ← Array.update s17 17#usize i80
  let i81 ← i67 >>> 42#i32
  let i82 ← lift (UScalar.cast .U8 i81)
  let s19 ← Array.update s18 18#usize i82
  let i83 ← i67 >>> 50#i32
  let i84 ← Array.index_usize limbs9 3#usize
  let i85 ← i84 <<< 1#i32
  let i86 ← lift (i83 ||| i85)
  let i87 ← lift (UScalar.cast .U8 i86)
  let s20 ← Array.update s19 19#usize i87
  let i88 ← i84 >>> 7#i32
  let i89 ← lift (UScalar.cast .U8 i88)
  let s21 ← Array.update s20 20#usize i89
  let i90 ← i84 >>> 15#i32
  let i91 ← lift (UScalar.cast .U8 i90)
  let s22 ← Array.update s21 21#usize i91
  let i92 ← i84 >>> 23#i32
  let i93 ← lift (UScalar.cast .U8 i92)
  let s23 ← Array.update s22 22#usize i93
  let i94 ← i84 >>> 31#i32
  let i95 ← lift (UScalar.cast .U8 i94)
  let s24 ← Array.update s23 23#usize i95
  let i96 ← i84 >>> 39#i32
  let i97 ← lift (UScalar.cast .U8 i96)
  let s25 ← Array.update s24 24#usize i97
  let i98 ← i84 >>> 47#i32
  let i99 ← Array.index_usize limbs9 4#usize
  let i100 ← i99 <<< 4#i32
  let i101 ← lift (i98 ||| i100)
  let i102 ← lift (UScalar.cast .U8 i101)
  let s26 ← Array.update s25 25#usize i102
  let i103 ← i99 >>> 4#i32
  let i104 ← lift (UScalar.cast .U8 i103)
  let s27 ← Array.update s26 26#usize i104
  let i105 ← i99 >>> 12#i32
  let i106 ← lift (UScalar.cast .U8 i105)
  let s28 ← Array.update s27 27#usize i106
  let i107 ← i99 >>> 20#i32
  let i108 ← lift (UScalar.cast .U8 i107)
  let s29 ← Array.update s28 28#usize i108
  let i109 ← i99 >>> 28#i32
  let i110 ← lift (UScalar.cast .U8 i109)
  let s30 ← Array.update s29 29#usize i110
  let i111 ← i99 >>> 36#i32
  let i112 ← lift (UScalar.cast .U8 i111)
  let s31 ← Array.update s30 30#usize i112
  let i113 ← i99 >>> 44#i32
  let i114 ← lift (UScalar.cast .U8 i113)
  let s32 ← Array.update s31 31#usize i114
  let i115 ← Array.index_usize s32 31#usize
  let i116 ← lift (i115 &&& 128#u8)
  massert (i116 = 0#u8)
  ok s32

set_option maxRecDepth 4096 in
/-- `to_bytes` is `reduce`, then `to_bytes_q`, `to_bytes_carry` and `to_bytes_pack`. -/
theorem to_bytes_unfold (self : FieldElement51) :
    to_bytes self =
      (do let fe ← reduce self
          let i ← Array.index_usize fe 0#usize
          let q4 ← to_bytes_q fe i
          let limbs9 ← to_bytes_carry fe i q4
          to_bytes_pack limbs9) := by
  rw [to_bytes]
  simp only [to_bytes_q, to_bytes_carry, to_bytes_pack, Std.bind_assoc, Std.bind_ok]


/-- Packing, bytes 0 to 6. -/
def to_bytes_pack0 (limbs9 : FieldElement51) : Result (Array U8 32#usize × U64) := do
  let s := Array.repeat 32#usize 0#u8
  let i39 ← Array.index_usize limbs9 0#usize
  let i40 ← lift (UScalar.cast .U8 i39)
  let s1 ← Array.update s 0#usize i40
  let i41 ← i39 >>> 8#i32
  let i42 ← lift (UScalar.cast .U8 i41)
  let s2 ← Array.update s1 1#usize i42
  let i43 ← i39 >>> 16#i32
  let i44 ← lift (UScalar.cast .U8 i43)
  let s3 ← Array.update s2 2#usize i44
  let i45 ← i39 >>> 24#i32
  let i46 ← lift (UScalar.cast .U8 i45)
  let s4 ← Array.update s3 3#usize i46
  let i47 ← i39 >>> 32#i32
  let i48 ← lift (UScalar.cast .U8 i47)
  let s5 ← Array.update s4 4#usize i48
  let i49 ← i39 >>> 40#i32
  let i50 ← lift (UScalar.cast .U8 i49)
  let s6 ← Array.update s5 5#usize i50
  let i51 ← i39 >>> 48#i32
  let i52 ← Array.index_usize limbs9 1#usize
  let i53 ← i52 <<< 3#i32
  let i54 ← lift (i51 ||| i53)
  let i55 ← lift (UScalar.cast .U8 i54)
  let s7 ← Array.update s6 6#usize i55
  ok (s7, i52)

/-- Packing, bytes 7 to 12. -/
def to_bytes_pack1 (limbs9 : FieldElement51) (s7 : Array U8 32#usize) (i52 : U64) :
    Result (Array U8 32#usize × U64) := do
  let i56 ← i52 >>> 5#i32
  let i57 ← lift (UScalar.cast .U8 i56)
  let s8 ← Array.update s7 7#usize i57
  let i58 ← i52 >>> 13#i32
  let i59 ← lift (UScalar.cast .U8 i58)
  let s9 ← Array.update s8 8#usize i59
  let i60 ← i52 >>> 21#i32
  let i61 ← lift (UScalar.cast .U8 i60)
  let s10 ← Array.update s9 9#usize i61
  let i62 ← i52 >>> 29#i32
  let i63 ← lift (UScalar.cast .U8 i62)
  let s11 ← Array.update s10 10#usize i63
  let i64 ← i52 >>> 37#i32
  let i65 ← lift (UScalar.cast .U8 i64)
  let s12 ← Array.update s11 11#usize i65
  let i66 ← i52 >>> 45#i32
  let i67 ← Array.index_usize limbs9 2#usize
  let i68 ← i67 <<< 6#i32
  let i69 ← lift (i66 ||| i68)
  let i70 ← lift (UScalar.cast .U8 i69)
  let s13 ← Array.update s12 12#usize i70
  ok (s13, i67)

/-- Packing, bytes 13 to 19. -/
def to_bytes_pack2 (limbs9 : FieldElement51) (s13 : Array U8 32#usize) (i67 : U64) :
    Result (Array U8 32#usize × U64) := do
  let i71 ← i67 >>> 2#i32
  let i72 ← lift (UScalar.cast .U8 i71)
  let s14 ← Array.update s13 13#usize i72
  let i73 ← i67 >>> 10#i32
  let i74 ← lift (UScalar.cast .U8 i73)
  let s15 ← Array.update s14 14#usize i74
  let i75 ← i67 >>> 18#i32
  let i76 ← lift (UScalar.cast .U8 i75)
  let s16 ← Array.update s15 15#usize i76
  let i77 ← i67 >>> 26#i32
  let i78 ← lift (UScalar.cast .U8 i77)
  let s17 ← Array.update s16 16#usize i78
  let i79 ← i67 >>> 34#i32
  let i80 ← lift (UScalar.cast .U8 i79)
  let s18 ← Array.update s17 17#usize i80
  let i81 ← i67 >>> 42#i32
  let i82 ← lift (UScalar.cast .U8 i81)
  let s19 ← Array.update s18 18#usize i82
  let i83 ← i67 >>> 50#i32
  let i84 ← Array.index_usize limbs9 3#usize
  let i85 ← i84 <<< 1#i32
  let i86 ← lift (i83 ||| i85)
  let i87 ← lift (UScalar.cast .U8 i86)
  let s20 ← Array.update s19 19#usize i87
  ok (s20, i84)

/-- Packing, bytes 20 to 25. -/
def to_bytes_pack3 (limbs9 : FieldElement51) (s20 : Array U8 32#usize) (i84 : U64) :
    Result (Array U8 32#usize × U64) := do
  let i88 ← i84 >>> 7#i32
  let i89 ← lift (UScalar.cast .U8 i88)
  let s21 ← Array.update s20 20#usize i89
  let i90 ← i84 >>> 15#i32
  let i91 ← lift (UScalar.cast .U8 i90)
  let s22 ← Array.update s21 21#usize i91
  let i92 ← i84 >>> 23#i32
  let i93 ← lift (UScalar.cast .U8 i92)
  let s23 ← Array.update s22 22#usize i93
  let i94 ← i84 >>> 31#i32
  let i95 ← lift (UScalar.cast .U8 i94)
  let s24 ← Array.update s23 23#usize i95
  let i96 ← i84 >>> 39#i32
  let i97 ← lift (UScalar.cast .U8 i96)
  let s25 ← Array.update s24 24#usize i97
  let i98 ← i84 >>> 47#i32
  let i99 ← Array.index_usize limbs9 4#usize
  let i100 ← i99 <<< 4#i32
  let i101 ← lift (i98 ||| i100)
  let i102 ← lift (UScalar.cast .U8 i101)
  let s26 ← Array.update s25 25#usize i102
  ok (s26, i99)

/-- Packing, bytes 26 to 31, and the check of the top bit. -/
def to_bytes_pack4 (s26 : Array U8 32#usize) (i99 : U64) : Result (Array U8 32#usize) := do
  let i103 ← i99 >>> 4#i32
  let i104 ← lift (UScalar.cast .U8 i103)
  let s27 ← Array.update s26 26#usize i104
  let i105 ← i99 >>> 12#i32
  let i106 ← lift (UScalar.cast .U8 i105)
  let s28 ← Array.update s27 27#usize i106
  let i107 ← i99 >>> 20#i32
  let i108 ← lift (UScalar.cast .U8 i107)
  let s29 ← Array.update s28 28#usize i108
  let i109 ← i99 >>> 28#i32
  let i110 ← lift (UScalar.cast .U8 i109)
  let s30 ← Array.update s29 29#usize i110
  let i111 ← i99 >>> 36#i32
  let i112 ← lift (UScalar.cast .U8 i111)
  let s31 ← Array.update s30 30#usize i112
  let i113 ← i99 >>> 44#i32
  let i114 ← lift (UScalar.cast .U8 i113)
  let s32 ← Array.update s31 31#usize i114
  let i115 ← Array.index_usize s32 31#usize
  let i116 ← lift (i115 &&& 128#u8)
  massert (i116 = 0#u8)
  ok s32


set_option maxRecDepth 4096 in
/-- `to_bytes_pack` is `to_bytes_pack0` to `to_bytes_pack4` in sequence. -/
theorem to_bytes_pack_unfold (L : FieldElement51) :
    to_bytes_pack L =
      (do let r0 ← to_bytes_pack0 L
          let r1 ← to_bytes_pack1 L r0.1 r0.2
          let r2 ← to_bytes_pack2 L r1.1 r1.2
          let r3 ← to_bytes_pack3 L r2.1 r2.2
          to_bytes_pack4 r3.1 r3.2) := by
  rw [to_bytes_pack]
  simp only [to_bytes_pack0, to_bytes_pack1, to_bytes_pack2, to_bytes_pack3, to_bytes_pack4,
    Std.bind_assoc, Std.bind_ok]

/-- `bytes_match_limbs`, bytes 0 to 6. -/
def bm0 (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  s.val[0]!.val = L.val[0]!.val % 2^8 ∧
  s.val[1]!.val = L.val[0]!.val >>> 8 % 2^8 ∧
  s.val[2]!.val = L.val[0]!.val >>> 16 % 2^8 ∧
  s.val[3]!.val = L.val[0]!.val >>> 24 % 2^8 ∧
  s.val[4]!.val = L.val[0]!.val >>> 32 % 2^8 ∧
  s.val[5]!.val = L.val[0]!.val >>> 40 % 2^8 ∧
  s.val[6]!.val = (L.val[0]!.val >>> 48 ||| L.val[1]!.val <<< 3 % U64.size) % 2^8
/-- `bytes_match_limbs`, bytes 7 to 12. -/
def bm1 (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  s.val[7]!.val = L.val[1]!.val >>> 5 % 2^8 ∧
  s.val[8]!.val = L.val[1]!.val >>> 13 % 2^8 ∧
  s.val[9]!.val = L.val[1]!.val >>> 21 % 2^8 ∧
  s.val[10]!.val = L.val[1]!.val >>> 29 % 2^8 ∧
  s.val[11]!.val = L.val[1]!.val >>> 37 % 2^8 ∧
  s.val[12]!.val = (L.val[1]!.val >>> 45 ||| L.val[2]!.val <<< 6 % U64.size) % 2^8
/-- `bytes_match_limbs`, bytes 13 to 19. -/
def bm2 (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  s.val[13]!.val = L.val[2]!.val >>> 2 % 2^8 ∧
  s.val[14]!.val = L.val[2]!.val >>> 10 % 2^8 ∧
  s.val[15]!.val = L.val[2]!.val >>> 18 % 2^8 ∧
  s.val[16]!.val = L.val[2]!.val >>> 26 % 2^8 ∧
  s.val[17]!.val = L.val[2]!.val >>> 34 % 2^8 ∧
  s.val[18]!.val = L.val[2]!.val >>> 42 % 2^8 ∧
  s.val[19]!.val = (L.val[2]!.val >>> 50 ||| L.val[3]!.val <<< 1 % U64.size) % 2^8
/-- `bytes_match_limbs`, bytes 20 to 25. -/
def bm3 (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  s.val[20]!.val = L.val[3]!.val >>> 7 % 2^8 ∧
  s.val[21]!.val = L.val[3]!.val >>> 15 % 2^8 ∧
  s.val[22]!.val = L.val[3]!.val >>> 23 % 2^8 ∧
  s.val[23]!.val = L.val[3]!.val >>> 31 % 2^8 ∧
  s.val[24]!.val = L.val[3]!.val >>> 39 % 2^8 ∧
  s.val[25]!.val = (L.val[3]!.val >>> 47 ||| L.val[4]!.val <<< 4 % U64.size) % 2^8
/-- `bytes_match_limbs`, bytes 26 to 31. -/
def bm4 (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  s.val[26]!.val = L.val[4]!.val >>> 4 % 2^8 ∧
  s.val[27]!.val = L.val[4]!.val >>> 12 % 2^8 ∧
  s.val[28]!.val = L.val[4]!.val >>> 20 % 2^8 ∧
  s.val[29]!.val = L.val[4]!.val >>> 28 % 2^8 ∧
  s.val[30]!.val = L.val[4]!.val >>> 36 % 2^8 ∧
  s.val[31]!.val = L.val[4]!.val >>> 44 % 2^8

/-- Setting byte `k` leaves byte `j ≠ k` unchanged. -/
theorem u8x32_set_ne (s : Array U8 32#usize) (k : Usize) (x : U8) (j : Nat) (h : j ≠ k.val) :
    (s.set k x).val[j]! = s.val[j]! := by
  rw [Array.set_val_eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]


/-- `to_bytes_pack0 L` writes bytes 0 to 6 as in `bm0`, and returns limb 1. -/
theorem to_bytes_pack0_spec (L : FieldElement51) :
    to_bytes_pack0 L ⦃ (r : Array U8 32#usize × U64) => r.2 = L.val[1]! ∧ bm0 L r.1 ⦄ := by
  unfold to_bytes_pack0
  have hlen : L.val.length = 5 := by simp
  have e0 : L.val[0]! = L.val[0] := getElem!_pos L.val 0 (by omega)
  have e1 : L.val[1]! = L.val[1] := getElem!_pos L.val 1 (by omega)
  step*
  refine ⟨by rw [e1]; exact i52_post, ?_⟩
  unfold bm0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.getElem_set_self,
      List.getElem_set_ne, ne_eq, not_false_eq_true, UScalar.ofNatCore_val_eq, U64_cast_U8,
      UScalar.val_or, Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
      Nat.reduceEqDiff, Nat.succ_ne_self, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
      Array.repeat_val, List.length_replicate, Array.length, *]


/-- Given limb 1, `to_bytes_pack1` writes bytes 7 to 12 as in `bm1`, keeps bytes 0 to 6,
and returns limb 2. -/
theorem to_bytes_pack1_spec (L : FieldElement51) (s7 : Array U8 32#usize) (i52 : U64)
    (h : i52 = L.val[1]!) :
    to_bytes_pack1 L s7 i52 ⦃ (r : Array U8 32#usize × U64) =>
      r.2 = L.val[2]! ∧ bm1 L r.1 ∧ ∀ j < 7, r.1.val[j]! = s7.val[j]! ⦄ := by
  unfold to_bytes_pack1
  have hlen : L.val.length = 5 := by simp
  have e1 : L.val[1]! = L.val[1] := getElem!_pos L.val 1 (by omega)
  have e2 : L.val[2]! = L.val[2] := getElem!_pos L.val 2 (by omega)
  subst h
  have hs : s7.val.length = 32 := by simp
  step*
  refine ⟨by rw [e2]; exact i67_post, ?_, ?_⟩
  · unfold bm1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.getElem_set_self,
      List.getElem_set_ne, ne_eq, not_false_eq_true, UScalar.ofNatCore_val_eq, U64_cast_U8,
      UScalar.val_or, Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
      Nat.reduceEqDiff, Nat.succ_ne_self, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
      Array.repeat_val, List.length_replicate, Array.length, *]
  · intro j hj
    simp only [s13_post, s12_post, s11_post, s10_post, s9_post, s8_post]
    rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)];

/-- Given limb 2, `to_bytes_pack2` writes bytes 13 to 19 as in `bm2`, keeps bytes 0 to 12,
and returns limb 3. -/
theorem to_bytes_pack2_spec (L : FieldElement51) (s13 : Array U8 32#usize) (i67 : U64)
    (h : i67 = L.val[2]!) :
    to_bytes_pack2 L s13 i67 ⦃ (r : Array U8 32#usize × U64) =>
      r.2 = L.val[3]! ∧ bm2 L r.1 ∧ ∀ j < 13, r.1.val[j]! = s13.val[j]! ⦄ := by
  unfold to_bytes_pack2
  have hlen : L.val.length = 5 := by simp
  have e2 : L.val[2]! = L.val[2] := getElem!_pos L.val 2 (by omega)
  have e3 : L.val[3]! = L.val[3] := getElem!_pos L.val 3 (by omega)
  subst h
  have hs : s13.val.length = 32 := by simp
  step*
  refine ⟨by rw [e3]; exact i84_post, ?_, ?_⟩
  · unfold bm2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.getElem_set_self,
      List.getElem_set_ne, ne_eq, not_false_eq_true, UScalar.ofNatCore_val_eq, U64_cast_U8,
      UScalar.val_or, Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
      Nat.reduceEqDiff, Nat.succ_ne_self, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
      Array.repeat_val, List.length_replicate, Array.length, *]
  · intro j hj
    simp only [s20_post, s19_post, s18_post, s17_post, s16_post, s15_post, s14_post]
    rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)];

/-- Given limb 3, `to_bytes_pack3` writes bytes 20 to 25 as in `bm3`, keeps bytes 0 to 19,
and returns limb 4. -/
theorem to_bytes_pack3_spec (L : FieldElement51) (s20 : Array U8 32#usize) (i84 : U64)
    (h : i84 = L.val[3]!) :
    to_bytes_pack3 L s20 i84 ⦃ (r : Array U8 32#usize × U64) =>
      r.2 = L.val[4]! ∧ bm3 L r.1 ∧ ∀ j < 20, r.1.val[j]! = s20.val[j]! ⦄ := by
  unfold to_bytes_pack3
  have hlen : L.val.length = 5 := by simp
  have e3 : L.val[3]! = L.val[3] := getElem!_pos L.val 3 (by omega)
  have e4 : L.val[4]! = L.val[4] := getElem!_pos L.val 4 (by omega)
  subst h
  have hs : s20.val.length = 32 := by simp
  step*
  refine ⟨by rw [e4]; exact i99_post, ?_, ?_⟩
  · unfold bm3
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.getElem_set_self,
      List.getElem_set_ne, ne_eq, not_false_eq_true, UScalar.ofNatCore_val_eq, U64_cast_U8,
      UScalar.val_or, Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
      Nat.reduceEqDiff, Nat.succ_ne_self, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
      Array.repeat_val, List.length_replicate, Array.length, *]
  · intro j hj
    simp only [s26_post, s25_post, s24_post, s23_post, s22_post, s21_post]
    rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)];


/-- Given limb 4 below `2 ^ 51`, `to_bytes_pack4` writes bytes 26 to 31 as in `bm4`, keeps
bytes 0 to 25, and its top-bit check succeeds. -/
theorem to_bytes_pack4_spec (L : FieldElement51) (s26 : Array U8 32#usize) (i99 : U64)
    (h : i99 = L.val[4]!) (hb : (L.val[4]! : U64).val < 2 ^ 51) :
    to_bytes_pack4 s26 i99 ⦃ (r : Array U8 32#usize) =>
      bm4 L r ∧ ∀ j < 26, r.val[j]! = s26.val[j]! ⦄ := by
  unfold to_bytes_pack4
  have hs : s26.val.length = 32 := by simp
  subst h
  step*
  · have h115 : i115 = i114 := by
      simp only [i115_post, s32_post, Array.set_val_eq, UScalar.ofNatCore_val_eq,
        List.getElem_set_self]
    have h113 : i113.val < 128 := by
      rw [i113_post, Nat.shiftRight_eq_div_pow]; omega
    have h114 : i114.val < 128 := by
      simp only [i114_post, U64_cast_U8]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h113
    have : i116.val = 0 := by
      rw [i116_post, h115]; exact u8_and_128_eq_zero_of_lt i114 h114
    exact UScalar.eq_of_val_eq this
  refine ⟨?_, ?_⟩
  · unfold bm4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.getElem_set_self,
        List.getElem_set_ne, ne_eq, not_false_eq_true, UScalar.ofNatCore_val_eq, U64_cast_U8,
        UScalar.val_or, Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
        Nat.reduceEqDiff, Nat.succ_ne_self, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
        Array.repeat_val, List.length_replicate, Array.length, *]
  · intro j hj
    simp only [s32_post, s31_post, s30_post, s29_post, s28_post, s27_post]
    rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)]; rw [u8x32_set_ne _ _ _ _ (by simp; omega)];

/-- For limbs below `2 ^ 51`, `to_bytes_pack L` returns `s` with
`U8x32_as_Nat s = Field51_as_Nat L`. -/
theorem to_bytes_pack_spec (L : FieldElement51) (hL : ∀ i < 5, L[i]!.val < 2 ^ 51) :
    to_bytes_pack L ⦃ (s : Array U8 32#usize) => U8x32_as_Nat s = Field51_as_Nat L ⦄ := by
  have hL' : ∀ i < 5, (L.val[i]! : U64).val < 2 ^ 51 := by
    intro i hi; have := hL i hi; rwa [Array.getElem!_Nat_eq] at this
  rw [to_bytes_pack_unfold]
  step with to_bytes_pack0_spec as ⟨r0, h0, b0⟩
  step with to_bytes_pack1_spec as ⟨r1, h1, b1, p1⟩
  step with to_bytes_pack2_spec as ⟨r2, h2, b2, p2⟩
  step with to_bytes_pack3_spec as ⟨r3, h3, b3, p3⟩
  step with to_bytes_pack4_spec L r3.1 r3.2 h3 (hL' 4 (by omega)) as ⟨r4, b4, p4⟩
  apply byte_packing_eq L r4 hL'
  unfold bm0 at b0; unfold bm1 at b1; unfold bm2 at b2; unfold bm3 at b3; unfold bm4 at b4
  have q3 : ∀ j < 20, r4.val[j]! = r2.1.val[j]! := fun j hj => by
    rw [p4 j (by omega), p3 j hj]
  have q2 : ∀ j < 13, r4.val[j]! = r1.1.val[j]! := fun j hj => by
    rw [q3 j (by omega), p2 j hj]
  have q1 : ∀ j < 7, r4.val[j]! = r0.1.val[j]! := fun j hj => by
    rw [q2 j (by omega), p1 j hj]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := b0
  obtain ⟨a7, a8, a9, a10, a11, a12⟩ := b1
  obtain ⟨a13, a14, a15, a16, a17, a18, a19⟩ := b2
  obtain ⟨a20, a21, a22, a23, a24, a25⟩ := b3
  obtain ⟨a26, a27, a28, a29, a30, a31⟩ := b4
  unfold bytes_match_limbs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [q1]; assumption; omega)
    | (rw [q2]; assumption; omega)
    | (rw [q3]; assumption; omega)
    | (rw [p4]; assumption; omega)
    | assumption


/-- For limbs below `2 ^ 52`, `to_bytes_q` returns `q = ⌊(F + 19) / 2 ^ 255⌋` as a carry chain,
where `F = Field51_as_Nat fe`, and `q ≤ 2`. -/
theorem to_bytes_q_spec (fe : FieldElement51) (i : U64) (hi : i = fe.val[0]!)
    (hfe : ∀ k < 5, (fe.val[k]! : U64).val < 2 ^ 52) :
    to_bytes_q fe i ⦃ (q4 : U64) =>
      q4.val = (((((fe.val[0]!.val + 19) / 2 ^ 51 + fe.val[1]!.val) / 2 ^ 51 +
        fe.val[2]!.val) / 2 ^ 51 + fe.val[3]!.val) / 2 ^ 51 + fe.val[4]!.val) / 2 ^ 51 ∧
      q4.val ≤ 2 ⦄ := by
  unfold to_bytes_q
  have hlen : fe.val.length = 5 := by simp
  have e1 : fe.val[1]! = fe.val[1] := getElem!_pos fe.val 1 (by omega)
  have e2 : fe.val[2]! = fe.val[2] := getElem!_pos fe.val 2 (by omega)
  have e3 : fe.val[3]! = fe.val[3] := getElem!_pos fe.val 3 (by omega)
  have e4 : fe.val[4]! = fe.val[4] := getElem!_pos fe.val 4 (by omega)
  have h0 := hfe 0 (by omega); have h1 := hfe 1 (by omega); have h2 := hfe 2 (by omega)
  have h3 := hfe 3 (by omega); have h4 := hfe 4 (by omega)
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4
  subst hi
  step*
  all_goals
    simp only [Nat.shiftRight_eq_div_pow, e1, e2, e3, e4] at *
    subst_vars
  all_goals scalar_tac


/-- For limbs below `2 ^ 52` and `q ≤ 2`, `to_bytes_carry` returns the carry chain of
`fe + 19 q`, each limb reduced mod `2 ^ 51`. -/
theorem to_bytes_carry_spec (fe : FieldElement51) (i q4 : U64) (hi : i = fe.val[0]!)
    (hfe : ∀ k < 5, (fe.val[k]! : U64).val < 2 ^ 52) (hq : q4.val ≤ 2) :
    to_bytes_carry fe i q4 ⦃ (L : FieldElement51) =>
      let f0 := fe.val[0]!.val; let f1 := fe.val[1]!.val; let f2 := fe.val[2]!.val
      let f3 := fe.val[3]!.val; let f4 := fe.val[4]!.val
      L.val[0]!.val = (f0 + 19 * q4.val) % 2 ^ 51 ∧
      L.val[1]!.val = (f1 + (f0 + 19 * q4.val) / 2 ^ 51) % 2 ^ 51 ∧
      L.val[2]!.val = (f2 + (f1 + (f0 + 19 * q4.val) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      L.val[3]!.val =
        (f3 + (f2 + (f1 + (f0 + 19 * q4.val) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      L.val[4]!.val =
        (f4 + (f3 + (f2 + (f1 + (f0 + 19 * q4.val) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) %
          2 ^ 51 ⦄ := by
  unfold to_bytes_carry
  have hlen : fe.val.length = 5 := by simp
  have e0 : fe.val[0]! = fe.val[0] := getElem!_pos fe.val 0 (by omega)
  have e1 : fe.val[1]! = fe.val[1] := getElem!_pos fe.val 1 (by omega)
  have e2 : fe.val[2]! = fe.val[2] := getElem!_pos fe.val 2 (by omega)
  have e3 : fe.val[3]! = fe.val[3] := getElem!_pos fe.val 3 (by omega)
  have e4 : fe.val[4]! = fe.val[4] := getElem!_pos fe.val 4 (by omega)
  have h0 := hfe 0 (by omega); have h1 := hfe 1 (by omega); have h2 := hfe 2 (by omega)
  have h3 := hfe 3 (by omega); have h4 := hfe 4 (by omega)
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4
  clear hfe e0 e1 e2 e3 e4
  subst hi
  step*
  all_goals
    simp_all only [Array.set_val_eq, List.getElem_set_self, List.getElem_set_ne, getElem!_pos,
      List.length_set, ne_eq, not_false_eq_true, UScalar.ofNatCore_val_eq, Nat.reduceEqDiff,
      Nat.succ_ne_self, one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, zero_ne_one,
      OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Nat.reduceLT, Nat.lt_add_one, Nat.ofNat_pos,
      Nat.one_lt_ofNat, Nat.shiftRight_eq_div_pow, UScalar.val_and]
  all_goals try scalar_tac
  have hm : (1 <<< 51 % U64.size - 1 : Nat) = 2 ^ 51 - 1 := by
    simp only [U64.size, U64.numBits, UScalarTy.U64_numBits_eq]; norm_num [Nat.shiftLeft_eq]
  simp only [hm, land_pow_two_sub_one_eq_mod, and_self]


/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::to_bytes`**
• The function always succeeds (no panic)
• `U8x32_as_Nat result ≡ Field51_as_Nat self (mod p)`,
  i.e. the byte encoding agrees with the limb encoding modulo `p`
• The returned 32-byte value is canonical (`< p`)
-/
@[step]
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    to_bytes self ⦃ (result : Array U8 32#usize) =>
      U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
      U8x32_as_Nat result < p ⦄ := by
  rw [to_bytes_unfold]
  step with reduce_spec as ⟨fe, hb, hmod, hlt⟩
  have hfe : ∀ k < 5, (fe.val[k]! : U64).val < 2 ^ 52 := by
    intro k hk; have := hb k hk; rwa [Array.getElem!_Nat_eq] at this
  step with Array.index_usize_spec as ⟨i, hi⟩
  have hi' : i = fe.val[0]! := by
    rw [hi]; exact (getElem!_pos fe.val 0 (by simp)).symm
  step with to_bytes_q_spec fe i hi' hfe as ⟨q4, hq, hq2⟩
  step with to_bytes_carry_spec fe i q4 hi' hfe hq2 as ⟨L, hl0, hl1, hl2, hl3, hl4⟩
  have hL : ∀ k < 5, L[k]!.val < 2 ^ 51 := by
    intro k hk; rw [Array.getElem!_Nat_eq]
    interval_cases k
    · rw [hl0]; exact Nat.mod_lt _ (by norm_num)
    · rw [hl1]; exact Nat.mod_lt _ (by norm_num)
    · rw [hl2]; exact Nat.mod_lt _ (by norm_num)
    · rw [hl3]; exact Nat.mod_lt _ (by norm_num)
    · rw [hl4]; exact Nat.mod_lt _ (by norm_num)
  step with to_bytes_pack_spec L hL as ⟨s, hs⟩
  rw [hs]
  have hF : fe.val[0]!.val + 2 ^ 51 * fe.val[1]!.val + 2 ^ 102 * fe.val[2]!.val +
      2 ^ 153 * fe.val[3]!.val + 2 ^ 204 * fe.val[4]!.val < 2 * (2 ^ 255 - 19) := by
    simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      Nat.reduceMul, zero_add, Array.getElem!_Nat_eq, p] at hlt
    omega
  obtain ⟨hcm, hcl⟩ := canonical_reduction_mod_p _ _ _ _ _ hF _ hq _ _ _ _ _ hl0 hl1 hl2 hl3 hl4
  have eL : Field51_as_Nat L = L.val[0]!.val + 2 ^ 51 * L.val[1]!.val + 2 ^ 102 * L.val[2]!.val +
      2 ^ 153 * L.val[3]!.val + 2 ^ 204 * L.val[4]!.val := by
    simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      Nat.reduceMul, zero_add, Array.getElem!_Nat_eq]; ring
  have eF : Field51_as_Nat fe = fe.val[0]!.val + 2 ^ 51 * fe.val[1]!.val +
      2 ^ 102 * fe.val[2]!.val + 2 ^ 153 * fe.val[3]!.val + 2 ^ 204 * fe.val[4]!.val := by
    simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      Nat.reduceMul, zero_add, Array.getElem!_Nat_eq]; ring
  rw [← eL, ← eF] at hcm; rw [← eL] at hcl
  exact ⟨hcm.trans hmod.symm, hcl⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51
