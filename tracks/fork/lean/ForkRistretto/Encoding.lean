import ForkRistretto.SqrtRatio
import Curve25519.Proofs.Ristretto.Algebra
import Proofs.Helpers.RistrettoCompress

/-! # The reference `decode` and `encode` are the fork's `decodeRep` and `encodeRep`

`decode_spec`: for every 32-byte input `b`, the reference `decode b` rejects `b` exactly when
the fork's `Ristretto.decodeRep (b.asNat 8)` is `none`. Otherwise it returns `(x, y, 1, x y)`
for the point `(x, y)` of `decodeRep`. The two follow RFC 9496, section 4.3.1, step by step.

`encode_spec`: if the extended coordinates `(X, Y, Z, T)` represent a point `P` (`Z ≠ 0`,
`X Y = Z T`, `P = (X / Z, Y / Z)`), the reference `encode` returns bytes whose value is the
fork's `Ristretto.encodeRep P`. The reference computes RFC 9496, section 4.3.2, on `(X, Y, Z, T)`.
This is the fork's `compressProj`, which the fork shows independent of the representative
(`compressProj_eq_encodeRep`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519

namespace ForkRistretto

/-- The extended coordinates of the reference. -/
abbrev RefPt := _root_.field.Fe × _root_.field.Fe × _root_.field.Fe × _root_.field.Fe

/-- The reference coordinates `(x, y, 1, x y)` of an affine point. -/
def refOf (P : edwards.Point) : RefPt :=
  (toF.symm P.x, toF.symm P.y, 1, toF.symm (P.x * P.y))

/-- The result of the reference `decode` against the result of `decodeRep`. -/
def DecRel : core.result.Result RefPt U8 → Option edwards.Point → Prop
  | .Ok q, some P => q = refOf P
  | .Err e, none => e = 20#u8
  | _, _ => False

theorem u32_val_one : (1#u32 : U32).val = 1 := rfl

theorem u32_val_zero : (0#u32 : U32).val = 0 := rfl

theorem decRel_err_none : DecRel (.Err ristretto_ref.DECODING_ERROR) none := by
  unfold ristretto_ref.DECODING_ERROR
  rfl

/-- The reference `decode` is the fork's `decodeRep`. -/
theorem decode_spec (b : Array U8 32#usize) :
    ristretto_ref.decode b ⦃ q => DecRel q (Ristretto.decodeRep (b.asNat 8)) ⦄ := by
  unfold ristretto_ref.decode
  rw [fe_from_bytes_eq, bind_ok]
  apply spec_bind (ref_geq_p_spec b)
  rintro _ rfl
  by_cases hp : p ≤ b.asNat 8
  · simp only [hp, decide_true, ite_true, spec_ok]
    rw [(Ristretto.decodeRep_eq_none_iff _).mpr (Or.inl hp)]
    exact decRel_err_none
  simp only [hp, decide_false, Bool.false_eq_true, ite_false]
  rw [ref_is_negative, bind_ok, toF_natCast]
  by_cases hn : ((b.asNat 8 : ℕ) : ZMod p).IsNeg
  · simp only [hn, decide_true, ite_true, spec_ok]
    rw [(Ristretto.decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl hn))]
    exact decRel_err_none
  simp only [hn, decide_false, Bool.false_eq_true, ite_false]
  simp only [_root_.field.fe_lit, _root_.field.fe_sq, _root_.field.fe_sub, _root_.field.fe_add,
    _root_.field.fe_mul, ref_d, ref_neg_fe, ref_sqrt_ratio_m1, ref_abs, ref_is_negative, ref_eq,
    bind_ok, map_mul, map_pow, map_neg, map_sub, map_add, RingEquiv.apply_symm_apply,
    toF_natCast, u32_val_one, u32_val_zero, Nat.cast_one, Nat.cast_zero, map_one, map_zero]
  simp only [Std.uncurry_apply_pair, RingEquiv.apply_symm_apply, ← two_mul]
  generalize hW : sqrtRatioM1 1 ((-(d * (1 - ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2) -
    (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2) * (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2) = W
  obtain ⟨w1, r⟩ := W
  dsimp only
  have hlt : b.asNat 8 < p := lt_of_not_ge hp
  have hnone : (w1 = false ∨
      ((2 * ((b.asNat 8 : ℕ) : ZMod p) * (r * (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2))).abs *
        ((1 - ((b.asNat 8 : ℕ) : ZMod p) ^ 2) * (r * (r * (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2)) *
          (-(d * (1 - ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2) -
            (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2)))).IsNeg ∨
      (1 - ((b.asNat 8 : ℕ) : ZMod p) ^ 2) * (r * (r * (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2)) *
          (-(d * (1 - ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2) -
            (1 + ((b.asNat 8 : ℕ) : ZMod p) ^ 2) ^ 2)) = 0) →
      DecRel (.Err ristretto_ref.DECODING_ERROR) (Ristretto.decodeRep (b.asNat 8)) := by
    intro h
    rw [(Ristretto.decodeRep_eq_none_iff _).mpr (Or.inr (Or.inr (by simp only [hW]; exact h)))]
    exact decRel_err_none
  generalize hs : ((b.asNat 8 : ℕ) : ZMod p) = s at hW hn hnone
  cases w1
  · simp only [Bool.false_eq_true, ite_false, spec_ok]
    exact hnone (Or.inl rfl)
  have hr := sqrtRatioM1_one_of_fst (by rw [hW])
  rw [hW] at hr
  by_cases hneg : ((2 * s * (r * (1 + s ^ 2))).abs *
      ((1 - s ^ 2) * (r * (r * (1 + s ^ 2)) * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2)))).IsNeg
  · simp only [hneg, decide_true, ite_true, spec_ok]
    exact hnone (Or.inr (Or.inl hneg))
  by_cases hy0 : (1 - s ^ 2) * (r * (r * (1 + s ^ 2)) * (-(d * (1 - s ^ 2) ^ 2) - (1 + s ^ 2) ^ 2)) = 0
  · simp only [hneg, eq_true hy0, decide_true, decide_false, ite_true, ite_false,
      Bool.false_eq_true, spec_ok]
    exact hnone (Or.inr (Or.inr hy0))
  simp only [hneg, hy0, decide_false, ite_true, ite_false, Bool.false_eq_true, spec_ok]
  have hdec : Ristretto.decodeRep (b.asNat 8) =
      some ⟨_, _, Ristretto.decodeRep_equation s r (by simpa using hr)⟩ := by
    rw [Ristretto.decodeRep_eq_some_iff, hs]
    exact ⟨hlt, hn, Proofs.decode_y_eq s r (by simpa using hr), ZMod.not_isNeg_abs _, hneg, hy0⟩
  rw [hdec]
  simp only [DecRel, refOf]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_)) <;>
  · apply toF.injective
    simp [hs]

/-- `Q = (X, Y, Z, T)` represents the point `P`: `Z ≠ 0`, `X Y = Z T` and `P = (X / Z, Y / Z)`,
in the fork's field. -/
def Rep (Q : RefPt) (P : edwards.Point) : Prop :=
  toF Q.2.2.1 ≠ 0 ∧ toF Q.1 * toF Q.2.1 = toF Q.2.2.1 * toF Q.2.2.2 ∧
    P.x = toF Q.1 / toF Q.2.2.1 ∧ P.y = toF Q.2.1 / toF Q.2.2.1

/-- The reference `encode` of a representative of `P` is the fork's `encodeRep P`. -/
theorem encode_spec (Q : RefPt) (P : edwards.Point) (h : Rep Q P) :
    ristretto_ref.encode Q ⦃ c => c.asNat 8 = Ristretto.encodeRep P ⦄ := by
  obtain ⟨X, Y, Z, T⟩ := Q
  obtain ⟨hZ, hT, hx, hy⟩ := h
  dsimp only at hZ hT hx hy
  rw [← Curve25519Dalek.RistrettoCompress.compressProj_eq_encodeRep P (c := invsqrtAMinusD) rfl hZ hT hx hy]
  unfold ristretto_ref.encode
  simp only [_root_.field.fe_lit, _root_.field.fe_sq, _root_.field.fe_sub, _root_.field.fe_add,
    _root_.field.fe_mul, ref_sqrt_m1, ref_invsqrt_a_minus_d, ref_neg_fe, ref_sqrt_ratio_m1,
    ref_abs, ref_is_negative, ref_select, bind_ok, Std.uncurry_apply_pair]
  obtain ⟨c, hc, hv⟩ := fe_to_bytes_val _
  rw [hc, spec_ok, hv, RingEquiv.apply_symm_apply]
  congr 1
  unfold Curve25519Dalek.RistrettoCompress.compressProj
  simp only [map_mul, map_sub, map_add, map_pow, map_neg, apply_ite toF,
    RingEquiv.apply_symm_apply, u32_val_one, Nat.cast_one, decide_eq_true_eq, map_one,
    mul_assoc]

end ForkRistretto
