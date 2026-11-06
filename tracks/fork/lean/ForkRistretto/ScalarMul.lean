import ForkRistretto.Encoding

/-! # The reference scalar multiplication in the fork's group

The reference `edwards.point_mul s Q` (hacspec edwards25519 `point_mul`) computes `s • P` in the
fork's group `curve25519.edwards.Point` (`point_mul_spec`), if `Q` represents `P` (`Rep`).

This is the proof of track D (`tracks/ristretto/lean/Sim/ScalarMul.lean`), moved from the group
`DalekSim.Edwards.Point dEd` of the shared library to the group of the fork and EllipticCurve.
Only `addExt_rep` changes: it compares the reference `point_add` with the fork's affine formulas
`addX` and `addY` (`add_x`, `add_y`), and takes the nonzero denominators from the completeness
of the model (`addDen₁_ne_zero`, `addDen₂_ne_zero`). So no isomorphism of the two groups is
needed. The loop proof is the one of track D.

The reference has no separate doubling. `point_mul` doubles with `point_add p p`, and the
addition is complete, so `addExt_rep` covers doubling. The loop adds the bits from bit 0 up:
before step `i`, the register represents `2^i • P` and the accumulator `(s mod 2^i) • P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519 TwistedEdwardsModel

namespace ForkRistretto

/-- The formula of the reference `point_add`. -/
noncomputable def addExt (P Q : RefPt) : RefPt :=
  let (x1, y1, z1, t1) := P
  let (x2, y2, z2, t2) := Q
  let a := (y1 - x1) * (y2 - x2)
  let b := (y1 + x1) * (y2 + x2)
  let c := t1 * 2 * toF.symm d * t2
  let dd := z1 * 2 * z2
  let e := b - a
  let f := dd - c
  let g := dd + c
  let h := b + a
  (e * f, g * h, f * g, e * h)

theorem u32_val_two : (2#u32 : U32).val = 2 := rfl

/-- The reference `point_add` is `addExt`. -/
theorem ref_point_add (P Q : RefPt) : ristretto_ref.edwards.point_add P Q = ok (addExt P Q) := by
  obtain ⟨x1, y1, z1, t1⟩ := P
  obtain ⟨x2, y2, z2, t2⟩ := Q
  unfold ristretto_ref.edwards.point_add
  simp only [ref_d, _root_.field.fe_lit, _root_.field.fe_sub, _root_.field.fe_add,
    _root_.field.fe_mul, bind_ok, Std.uncurry_apply_pair, u32_val_two, Nat.cast_ofNat]
  rfl

/-- The sum of two represented points is represented by `addExt`. -/
theorem addExt_rep {Q1 Q2 : RefPt} {P1 P2 : edwards.Point} (h1 : Rep Q1 P1) (h2 : Rep Q2 P2) :
    Rep (addExt Q1 Q2) (P1 + P2) := by
  obtain ⟨X1, Y1, Z1, T1⟩ := Q1
  obtain ⟨X2, Y2, Z2, T2⟩ := Q2
  obtain ⟨hZ1, hT1, hx1, hy1⟩ := h1
  obtain ⟨hZ2, hT2, hx2, hy2⟩ := h2
  simp only [Rep, addExt, map_mul, map_sub, map_add, RingEquiv.apply_symm_apply, map_ofNat]
    at hZ1 hT1 hx1 hy1 hZ2 hT2 hx2 hy2 ⊢
  rw [add_x, add_y, addX, addY, addDen₁, addDen₂, edwards_d, edwards_a_eq_neg_one]
  have hd1 := addDen₁_ne_zero P1 P2
  have hd2 := addDen₂_ne_zero P1 P2
  rw [addDen₁, edwards_d] at hd1
  rw [addDen₂, edwards_d] at hd2
  generalize toF X1 = X1 at *
  generalize toF Y1 = Y1 at *
  generalize toF Z1 = Z1 at *
  generalize toF T1 = T1 at *
  generalize toF X2 = X2 at *
  generalize toF Y2 = Y2 at *
  generalize toF Z2 = Z2 at *
  generalize toF T2 = T2 at *
  have hX1 : X1 = Z1 * P1.x := by rw [hx1]; field_simp
  have hY1 : Y1 = Z1 * P1.y := by rw [hy1]; field_simp
  have hX2 : X2 = Z2 * P2.x := by rw [hx2]; field_simp
  have hY2 : Y2 = Z2 * P2.y := by rw [hy2]; field_simp
  have hT1' : T1 = Z1 * (P1.x * P1.y) := by
    apply mul_left_cancel₀ hZ1
    rw [← hT1, hX1, hY1]
    ring
  have hT2' : T2 = Z2 * (P2.x * P2.y) := by
    apply mul_left_cancel₀ hZ2
    rw [← hT2, hX2, hY2]
    ring
  subst hX1 hY1 hX2 hY2 hT1' hT2'
  clear hx1 hy1 hx2 hy2 hT1 hT2
  generalize P1.x = x1 at *
  generalize P1.y = y1 at *
  generalize P2.x = x2 at *
  generalize P2.y = y2 at *
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero
  have hZ3 : (Z1 * 2 * Z2 - Z1 * (x1 * y1) * 2 * d * (Z2 * (x2 * y2))) *
      (Z1 * 2 * Z2 + Z1 * (x1 * y1) * 2 * d * (Z2 * (x2 * y2))) ≠ 0 := by
    have : (Z1 * 2 * Z2 - Z1 * (x1 * y1) * 2 * d * (Z2 * (x2 * y2))) *
        (Z1 * 2 * Z2 + Z1 * (x1 * y1) * 2 * d * (Z2 * (x2 * y2))) =
        (2 * Z1 * Z2) ^ 2 * (1 - d * x1 * x2 * y1 * y2) * (1 + d * x1 * x2 * y1 * y2) := by
      ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero h2 hZ1) hZ2)) hd2) hd1
  refine ⟨hZ3, by ring, ?_, ?_⟩
  · rw [div_eq_div_iff hd1 hZ3]; ring
  · rw [div_eq_div_iff hd2 hZ3]; ring

/-- The reference `point_identity` is `(0, 1, 1, 0)`. -/
theorem ref_point_identity :
    ristretto_ref.edwards.point_identity = ok ((0, 1, 1, 0) : RefPt) := by
  unfold ristretto_ref.edwards.point_identity
  simp only [_root_.field.fe_lit, bind_ok, u32_val_one, u32_val_zero, Nat.cast_one, Nat.cast_zero]

/-- `(0, 1, 1, 0)` represents the identity. -/
theorem rep_zero : Rep (0, 1, 1, 0) (0 : edwards.Point) := by
  simp only [Rep, map_zero, map_one]
  refine ⟨one_ne_zero, by ring, ?_, ?_⟩
  · rw [zero_x, zero_div]
  · rw [zero_y, div_one]

/-- One bit of the scalar: `n mod 2^(i+1)` adds `2^i` to `n mod 2^i` if bit `i` is set. -/
theorem mod_two_pow_succ' (n i : ℕ) :
    n % 2 ^ (i + 1) = n % 2 ^ i + (if n.testBit i then 2 ^ i else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> simp [h]

/-- The Lean `scalar.l` is the modulus of hacspec `Scalar`, which the Rust code gives in hex. -/
example : scalar.l = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed := by
  norm_num [scalar.l]

/-- The reference modulus `scalar.l` is the fork's `L`. -/
theorem scalar_l_eq : scalar.l = L := by
  rw [L_def]

/-- The value of a scalar: its canonical representative, below `l`. -/
def scVal (s : scalar.Scalar) : ℕ := (show ZMod scalar.l from s).val

/-- The loop of `point_mul` from step `i`, with `i + n = 256`. If the register `pp` represents
`2^i • P` and the accumulator `q` represents `(scVal s mod 2^i) • P`, the loop returns a
representative of `(scVal s mod 2^256) • P`. -/
theorem point_mul_loop_spec (s : scalar.Scalar) (P : edwards.Point) :
    ∀ n, ∀ (i : Usize), i.val + n = 256 → ∀ (pp q : RefPt),
      Rep pp ((2 ^ i.val) • P) → Rep q ((scVal s % 2 ^ i.val) • P) →
      ristretto_ref.edwards.point_mul_loop s pp q i ⦃ r => Rep r ((scVal s % 2 ^ 256) • P) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i hi pp q _ hq
    rw [ristretto_ref.edwards.point_mul_loop]
    have : ¬ i < 256#usize := by scalar_tac
    rw [ite_eq_right this, spec_ok]
    rwa [show i.val = 256 by omega] at hq
  | succ n ih =>
    intro i hi pp q hp hq
    rw [ristretto_ref.edwards.point_mul_loop]
    have hlt : i < 256#usize := by scalar_tac
    rw [ite_eq_left hlt]
    have hp2 : Rep (addExt pp pp) ((2 ^ (i.val + 1)) • P) := by
      rw [pow_succ, mul_two, add_nsmul]
      exact addExt_rep hp hp
    have h256 : i.val < 256 := by omega
    have hbit := mod_two_pow_succ' (scVal s) i.val
    by_cases hb : (scVal s).testBit i.val
    · have hb' : (show ZMod scalar.l from s).val.testBit i.val = true := hb
      simp only [scalar.sc_bit, h256, hb', bind_ok, ref_point_add, ↓reduceIte]
      step as ⟨i1, hi1⟩
      apply ih i1 (by omega) _ _ (by rw [hi1]; exact hp2)
      rw [hi1, hbit, ite_eq_left hb, add_nsmul]
      exact addExt_rep hq hp
    · have hb' : (show ZMod scalar.l from s).val.testBit i.val = false := by
        simpa [scVal] using hb
      simp only [scalar.sc_bit, h256, hb', bind_ok, ref_point_add, Bool.false_eq_true,
        ↓reduceIte]
      step as ⟨i1, hi1⟩
      apply ih i1 (by omega) _ _ (by rw [hi1]; exact hp2)
      rw [hi1, hbit, ite_eq_right hb, Nat.add_zero]
      exact hq

/-- The reference `point_mul s Q` computes `s • P`, where `s` is read as its canonical
representative below `l`. The input needs only to represent a point of the curve. -/
theorem point_mul_spec (s : scalar.Scalar) (Q : RefPt) (P : edwards.Point) (h : Rep Q P) :
    ristretto_ref.edwards.point_mul s Q ⦃ r => Rep r (scVal s • P) ⦄ := by
  simp only [ristretto_ref.edwards.point_mul, ref_point_identity, bind_ok]
  have hl : scVal s < 2 ^ 256 :=
    lt_trans (ZMod.val_lt (show ZMod scalar.l from s)) (by norm_num [scalar.l])
  rw [← Nat.mod_eq_of_lt hl]
  exact point_mul_loop_spec s P 256 0#usize (by simp) Q _ (by simpa using h)
    (by rw [show (0#usize).val = 0 by simp, pow_zero, Nat.mod_one, zero_nsmul]; exact rep_zero)

/-! ## The scalar

The reference reads a scalar as an element of `ZMod l`, so it multiplies by the canonical
representative below `l`. A caller that starts from a natural number `k`, for example the
value of 32 bytes, gets `(k mod l) • P`. This is `k • P` if `k < l`, or if `l • P = 0`. -/

/-- If `s = k` in `ZMod l`, the reference computes `(k mod l) • P`. -/
theorem point_mul_spec_nat (k : ℕ) (s : scalar.Scalar) (hs : ((k : ZMod scalar.l)) = s)
    (Q : RefPt) (P : edwards.Point) (h : Rep Q P) :
    ristretto_ref.edwards.point_mul s Q ⦃ r => Rep r ((k % scalar.l) • P) ⦄ := by
  have hv : scVal s = k % scalar.l := by
    rw [scVal, ← ZMod.val_natCast]
    exact congrArg ZMod.val hs.symm
  rw [← hv]
  exact point_mul_spec s Q P h

/-- If `s = k` in `ZMod l`, and `k < l` or `l • P = 0`, the reference computes `k • P`. -/
theorem point_mul_spec_of (k : ℕ) (s : scalar.Scalar) (hs : ((k : ZMod scalar.l)) = s)
    (Q : RefPt) (P : edwards.Point) (h : Rep Q P) (hk : k < L ∨ L • P = 0) :
    ristretto_ref.edwards.point_mul s Q ⦃ r => Rep r (k • P) ⦄ := by
  have e : (k % scalar.l) • P = k • P := by
    rw [scalar_l_eq]
    rcases hk with hk | hP
    · rw [Nat.mod_eq_of_lt hk]
    · conv_rhs => rw [← Nat.mod_add_div k L]
      rw [add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]
  rw [← e]
  exact point_mul_spec_nat k s hs Q P h

/-! ## The encoding of the product

The fork's group is the full group of the curve, so `k • P` and `(k mod l) • P` can differ. For an
even point `P` (`Even P`, the Ristretto representatives), they differ by a 4-torsion point:
`4 l • P = 0`. The Ristretto encoding does not see 4-torsion (`encodeRep_rel`), so the two
products have the same encoding. -/

/-- For an even point, `(k mod l) • P` and `k • P` have the same encoding. -/
theorem encodeRep_mod_nsmul {P : edwards.Point} (hP : Even P) (k : ℕ) :
    Ristretto.encodeRep ((k % L) • P) = Ristretto.encodeRep (k • P) := by
  have hk : Even (k • P) := by
    obtain ⟨r, rfl⟩ := hP
    exact ⟨k • r, nsmul_add r r k⟩
  have h4 := (even_iff_four_mul_L_nsmul P).mp hP
  refine (Ristretto.encodeRep_rel hk ?_).symm
  rw [TwistedEdwardsModel.rel_iff_sub_mem, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl,
    AddSubgroup.torsionBy.nsmul_iff]
  have e : k • P = (k % L) • P + (k / L) • (L • P) := by
    rw [smul_smul, ← add_nsmul, Nat.mod_add_div']
  rw [e, add_sub_cancel_left, smul_comm 4 (k / L), smul_smul 4 L, h4, smul_zero]

/-- If `Q` represents an even point `P`, the reference `encode (point_mul s Q)`, with `s = k` in
`ZMod l`, returns bytes whose value is the encoding of `k • P`. -/
theorem point_mul_encode_spec (k : ℕ) (s : scalar.Scalar) (hs : ((k : ZMod scalar.l)) = s)
    (Q : RefPt) (P : edwards.Point) (h : Rep Q P) (hP : Even P) :
    ristretto_ref.edwards.point_mul s Q ⦃ q =>
      ristretto_ref.encode q ⦃ c => c.asNat 8 = Ristretto.encodeRep (k • P) ⦄ ⦄ := by
  apply spec_mono (point_mul_spec_nat k s hs Q P h)
  intro q hq
  apply spec_mono (encode_spec q _ hq)
  intro c hc
  rw [hc, scalar_l_eq, encodeRep_mod_nsmul hP]

end ForkRistretto
