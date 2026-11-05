/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Math.Edwards.Representation

/-!
# `EdwardsPoint::to_montgomery`

`to_montgomery` returns the bytes of `u = (Z + Y) / (Z - Y)` mod `p`, and `u = 0` if `Z ≡ Y`,
because `invert 0 = 0`. This file states `u` mod `p`. It does not prove that `u` is the
u-coordinate of a point on the Montgomery curve.

Source: "curve25519-dalek/src/edwards.rs"

Port note (ref-impl-simulation, Aeneas d119a474): only the coordinate part of the spec is
ported. The statement keeps the equations for `u`. It drops the parts with
`fromEdwards`, `abs_montgomery` and `MontgomeryPoint.mkPoint`, and their helper lemmas, because
they need `Math/Montgomery/Representation.lean`, which is not ported. `step*` on this pin names
the postconditions of a call `x_post`, `x_post1`, ... instead of `x_post1`, `x_post2`, ..., so
the proof uses the new names. The hypotheses `Y, Z < 2^53` are dropped, because `IsValid`
gives them, and the postcondition adds `u < p`, from `to_bytes_spec`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.EdwardsPoint

/-- For a valid `self`, `to_montgomery self` returns bytes `u < p` with `u ≡ 0` if `Z ≡ Y`,
and `u Z ≡ u Y + (Z + Y)` otherwise (mod `p`). -/
@[step]
theorem to_montgomery_spec (self : EdwardsPoint) (hvalid : self.IsValid) :
    to_montgomery self ⦃ (mp : montgomery.MontgomeryPoint) =>
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let u := U8x32_as_Nat mp
      u < p ∧
      if Z % p = Y % p then
        u % p = 0
      else
        (u * Z) % p = (u * Y + (Z + Y)) % p ⦄ := by
  have h_Y_bounds := hvalid.Y_bounds
  have h_Z_bounds := hvalid.Z_bounds
  unfold to_montgomery
  (step*; try grind)
  · refine ⟨by assumption, ?_⟩
    split_ifs
    · rename_i h_zy
      have h_W_zero : Field51_as_Nat W % p = 0 := by
        rw [h_zy, ← Nat.ModEq] at W_post1
        conv_rhs at W_post1 => rw [← Nat.zero_add (Field51_as_Nat self.Y)]
        exact Nat.ModEq.add_right_cancel' (Field51_as_Nat self.Y) W_post1
      rw [a_post, u_post, Nat.mul_mod, fe_post1 h_W_zero, mul_zero, Nat.zero_mod]
    · rename_i h_zy
      have h_W_neq_zero : Field51_as_Nat W % p ≠ 0 := by
        intro h_contra
        rw [Nat.add_mod, h_contra, Nat.zero_add, Nat.mod_mod] at W_post1
        exact h_zy W_post1.symm
      have h_W_inv := fe_post h_W_neq_zero
      simp only [Nat.mul_mod_mod, Nat.mod_mul_mod] at h_W_inv
      ring_nf at h_W_inv
      have h_U_eq : Field51_as_Nat U = Field51_as_Nat self.Y + Field51_as_Nat self.Z := by
        unfold Field51_as_Nat
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [U_post i (Finset.mem_range.mp hi)]
        ring
      have h_elim : U8x32_as_Nat a * Field51_as_Nat W ≡
        Field51_as_Nat self.Y + Field51_as_Nat self.Z [MOD p] := by
        calc
          U8x32_as_Nat a * Field51_as_Nat W ≡
              Field51_as_Nat u * Field51_as_Nat W [MOD p] := by
                simpa using a_post.mul_right (Field51_as_Nat W)
          _ ≡ (Field51_as_Nat U * Field51_as_Nat fe) * Field51_as_Nat W [MOD p] := by
                simpa using u_post.mul_right (Field51_as_Nat W)
          _ ≡ Field51_as_Nat U [MOD p] := by
            rw [Nat.mul_assoc]
            simpa using @Nat.ModEq.mul_left p (Field51_as_Nat fe *
            Field51_as_Nat W) 1 (Field51_as_Nat U) h_W_inv
          _ ≡ Field51_as_Nat self.Y + Field51_as_Nat self.Z [MOD p] := by
                unfold Nat.ModEq; simp only [h_U_eq]
      rw [Nat.mul_mod, ← W_post1, Nat.add_mod, ← Nat.mul_mod, Nat.mul_add, ← Nat.ModEq]
      ring_nf
      have h_sum : U8x32_as_Nat a * (Field51_as_Nat W % p) +
          U8x32_as_Nat a * (Field51_as_Nat self.Y % p)
          ≡ U8x32_as_Nat a * Field51_as_Nat W +
              U8x32_as_Nat a * Field51_as_Nat self.Y [MOD p] :=
          (Nat.ModEq.mul_left (U8x32_as_Nat a) (Nat.mod_modEq (Field51_as_Nat W) p)).add
          (Nat.ModEq.mul_left (U8x32_as_Nat a) (Nat.mod_modEq (Field51_as_Nat self.Y) p))
      refine h_sum.trans ?_
      rw [Nat.add_comm]
      have h_full := Nat.ModEq.add_left (U8x32_as_Nat a * Field51_as_Nat self.Y) h_elim
      grind
end curve25519_dalek.edwards.EdwardsPoint
