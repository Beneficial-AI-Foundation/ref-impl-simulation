/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Mathlib.Data.Nat.ModEq

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::sub`

This function computes the difference `a - b` of two `FieldElement51` values modulo
`p = 2^255 - 19`. To avoid underflow, a multiple of p is added.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"

Port note (ref-impl-simulation, Aeneas d119a474): the last part of the proof is new. It
expands `Field51_as_Nat` with `Field51_as_Nat_expand` and closes the goal with
`modeq_of_add_mul_eq`, because the offsets add up to `16 * p`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithSubSharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
open backend.serial.u64.field

set_option maxRecDepth 4096 in
/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::sub`**
• The function always succeeds (no panic) provided `a[i].val < 2^63` and `b[i].val < 2^54`
• Every output limb is `< 2 ^ 52`
• `Field51_as_Nat result + Field51_as_Nat b ≡ Field51_as_Nat a (mod p)`,
  the field subtraction property — equivalently `result ≡ a - b (mod p)`
• To make the theorem more easily readable and provable, we make the bounds `a[i] < 2^63`
  and `b[i] < 2^54` are slightly looser than what is strictly
  required:
  - `a[0] ≤ 2^64 - 1 - 36028797018963664`, `a[i] ≤ 2^64 - 1 - 36028797018963952` for `i ≥ 1`
  - `b[0] ≤ 36028797018963664`, `b[i] ≤ 36028797018963952` for `i ≥ 1`
-/
@[step]
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 63) (hb : ∀ i < 5, b[i]!.val < 2 ^ 54) :
    sub a b ⦃ (d : FieldElement51) =>
      (∀ i < 5, d[i]!.val < 2 ^ 52) ∧
      (Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p ⦄ := by
  unfold sub
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ i1, i1_post ⟩ ← U64.add_spec
  case hmax =>
    have h := ha 0 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 0 (by scalar_tac)] at h
    rw [i_post]; scalar_tac
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post_1, i3_post_2 ⟩ ← U64.sub_spec
  case h =>
    have h := hb 0 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 0 (by scalar_tac)] at h
    rw [i2_post]; scalar_tac
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← U64.add_spec
  case hmax =>
    have h := ha 1 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 1 (by scalar_tac)] at h
    rw [i4_post]; scalar_tac
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post_1, i7_post_2 ⟩ ← U64.sub_spec
  case h =>
    have h := hb 1 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 1 (by scalar_tac)] at h
    rw [i6_post]; scalar_tac
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
  let* ⟨ i9, i9_post ⟩ ← U64.add_spec
  case hmax =>
    have h := ha 2 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 2 (by scalar_tac)] at h
    rw [i8_post]; scalar_tac
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
  let* ⟨ i11, i11_post_1, i11_post_2 ⟩ ← U64.sub_spec
  case h =>
    have h := hb 2 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 2 (by scalar_tac)] at h
    rw [i10_post]; scalar_tac
  let* ⟨ i12, i12_post ⟩ ← Array.index_usize_spec
  let* ⟨ i13, i13_post ⟩ ← U64.add_spec
  case hmax =>
    have h := ha 3 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 3 (by scalar_tac)] at h
    rw [i12_post]; scalar_tac
  let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
  let* ⟨ i15, i15_post_1, i15_post_2 ⟩ ← U64.sub_spec
  case h =>
    have h := hb 3 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 3 (by scalar_tac)] at h
    rw [i14_post]; scalar_tac
  let* ⟨ i16, i16_post ⟩ ← Array.index_usize_spec
  let* ⟨ i17, i17_post ⟩ ← U64.add_spec
  case hmax =>
    have h := ha 4 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 4 (by scalar_tac)] at h
    rw [i16_post]; scalar_tac
  let* ⟨ i18, i18_post ⟩ ← Array.index_usize_spec
  let* ⟨ i19, i19_post_1, i19_post_2 ⟩ ← U64.sub_spec
  case h =>
    have h := hb 4 (by omega)
    rw [Array.getElem!_Nat_eq, getElem!_pos _ 4 (by scalar_tac)] at h
    rw [i18_post]; scalar_tac
  let* ⟨ res, res_post_1, res_post_2 ⟩ ← reduce_spec
  refine ⟨by assumption, ?_⟩
  -- modular arithmetic property
  have htmp : Field51_as_Nat res + Field51_as_Nat b ≡
    Field51_as_Nat (Array.make 5#usize [i3, i7, i11, i15, i19]) + Field51_as_Nat b [MOD p] := by
    apply Nat.ModEq.add_right; apply Nat.ModEq.symm; assumption
  apply Nat.ModEq.trans htmp
  rw [Field51_as_Nat_expand, Field51_as_Nat_expand, Field51_as_Nat_expand]
  have e0 : (Array.make 5#usize [i3, i7, i11, i15, i19])[0]! = i3 := rfl
  have e1 : (Array.make 5#usize [i3, i7, i11, i15, i19])[1]! = i7 := rfl
  have e2 : (Array.make 5#usize [i3, i7, i11, i15, i19])[2]! = i11 := rfl
  have e3 : (Array.make 5#usize [i3, i7, i11, i15, i19])[3]! = i15 := rfl
  have e4 : (Array.make 5#usize [i3, i7, i11, i15, i19])[4]! = i19 := rfl
  rw [e0, e1, e2, e3, e4]
  have h0 : i3.val + b[0]!.val = a[0]!.val + 36028797018963664 := by
    rw [Array.getElem!_Nat_eq a 0, Array.getElem!_Nat_eq b 0, getElem!_pos _ 0 (by scalar_tac),
      getElem!_pos _ 0 (by scalar_tac)]; grind
  have h1 : i7.val + b[1]!.val = a[1]!.val + 36028797018963952 := by
    rw [Array.getElem!_Nat_eq a 1, Array.getElem!_Nat_eq b 1, getElem!_pos _ 1 (by scalar_tac),
      getElem!_pos _ 1 (by scalar_tac)]; grind
  have h2 : i11.val + b[2]!.val = a[2]!.val + 36028797018963952 := by
    rw [Array.getElem!_Nat_eq a 2, Array.getElem!_Nat_eq b 2, getElem!_pos _ 2 (by scalar_tac),
      getElem!_pos _ 2 (by scalar_tac)]; grind
  have h3 : i15.val + b[3]!.val = a[3]!.val + 36028797018963952 := by
    rw [Array.getElem!_Nat_eq a 3, Array.getElem!_Nat_eq b 3, getElem!_pos _ 3 (by scalar_tac),
      getElem!_pos _ 3 (by scalar_tac)]; grind
  have h4 : i19.val + b[4]!.val = a[4]!.val + 36028797018963952 := by
    rw [Array.getElem!_Nat_eq a 4, Array.getElem!_Nat_eq b 4, getElem!_pos _ 4 (by scalar_tac),
      getElem!_pos _ 4 (by scalar_tac)]; grind
  -- The offsets add up to `16 * p`.
  refine (modeq_of_add_mul_eq _ _ 16 p ?_).symm
  unfold p
  omega

end CoreOpsArithSubSharedAFieldElement51FieldElement51
end curve25519_dalek.Shared0FieldElement51.Insts
