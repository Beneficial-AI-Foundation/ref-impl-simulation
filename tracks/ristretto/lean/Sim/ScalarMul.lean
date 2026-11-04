import Sim.Decode
import DalekSim.Edwards

/-! # The reference scalar multiplication

The reference `edwards.point_mul s P` (hacspec edwards25519 `point_mul`) computes `s • P` in the
group `Point dEd` of edwards25519, under the map from extended to affine coordinates
(`point_mul_spec`). The extended coordinates `(X, Y, Z, T)` stand for the affine point
`(X / Z, Y / Z)`, with `Z ≠ 0` and `X Y = Z T` (`Rep`).

The reference has no separate doubling: `point_mul` doubles with `point_add p p`. So one lemma,
`addExt_rep`, covers addition and doubling. It uses the completeness of the affine addition,
so it needs no hypothesis that the two points differ. The loop adds the bits from bit 0 up:
before step `i`, the register represents `2^i • P` and the accumulator `(s mod 2^i) • P`.

The theorem assumes only that the input represents a point of the curve. The scalar is an
element of `ZMod l`. The last section relates it to a natural number `k`, for example the value
of 32 bytes. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace RistrettoSim

open DalekSim DalekSim.Edwards

/-- Extended coordinates `(X, Y, Z, T)` over `ZMod p`. -/
abbrev ExtPt := ZMod p × ZMod p × ZMod p × ZMod p

/-- `Q = (X, Y, Z, T)` represents the affine point `P = (X / Z, Y / Z)`, with `Z ≠ 0` and
`X Y = Z T`. -/
def Rep (Q : ExtPt) (P : Point dEd) : Prop :=
  Q.2.2.1 ≠ 0 ∧ Q.1 * Q.2.1 = Q.2.2.1 * Q.2.2.2 ∧ (Q.1 / Q.2.2.1, Q.2.1 / Q.2.2.1) = P.1

/-- The formula of the reference `point_add`, over `ZMod p`. It returns `RefPt`, the type of the
reference, which is `ExtPt` by definition. -/
def addExt (P Q : ExtPt) : RefPt :=
  let (x1, y1, z1, t1) := P
  let (x2, y2, z2, t2) := Q
  let a := (y1 - x1) * (y2 - x2)
  let b := (y1 + x1) * (y2 + x2)
  let c := t1 * 2 * dEd * t2
  let d := z1 * 2 * z2
  let e := b - a
  let f := d - c
  let g := d + c
  let h := b + a
  (e * f, g * h, f * g, e * h)

/-- The reference `point_add` is `addExt`. -/
theorem ref_point_add (P Q : RefPt) : ristretto_ref.edwards.point_add P Q = ok (addExt P Q) := by
  obtain ⟨x1, y1, z1, t1⟩ := P
  obtain ⟨x2, y2, z2, t2⟩ := Q
  have hd : ((nD : Nat) : _root_.field.Fe) = dEd := rfl
  simp [ristretto_ref.edwards.point_add, ref_d, hd, field.fe_lit, field.fe_sub, field.fe_add,
    field.fe_mul, addExt]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The sum of two represented points is represented by `addExt`. -/
theorem addExt_rep {Q1 Q2 : ExtPt} {P1 P2 : Point dEd} (h1 : Rep Q1 P1) (h2 : Rep Q2 P2) :
    Rep (addExt Q1 Q2) (P1 + P2) := by
  obtain ⟨⟨x1, y1⟩, hc1⟩ := P1
  obtain ⟨⟨x2, y2⟩, hc2⟩ := P2
  obtain ⟨X1, Y1, Z1, T1⟩ := Q1
  obtain ⟨X2, Y2, Z2, T2⟩ := Q2
  obtain ⟨hZ1, hT1, hA1⟩ := h1
  obtain ⟨hZ2, hT2, hA2⟩ := h2
  simp only [Prod.mk.injEq] at hA1 hA2 hZ1 hZ2 hT1 hT2
  obtain ⟨hx1, hy1⟩ := hA1
  obtain ⟨hx2, hy2⟩ := hA2
  rw [div_eq_iff hZ1] at hx1 hy1
  rw [div_eq_iff hZ2] at hx2 hy2
  subst hx1 hy1 hx2 hy2
  have hT1' : T1 = x1 * y1 * Z1 := by
    apply mul_left_cancel₀ hZ1; linear_combination -hT1
  have hT2' : T2 = x2 * y2 * Z2 := by
    apply mul_left_cancel₀ hZ2; linear_combination -hT2
  subst hT1' hT2'
  have hp := one_add_ne_zero hc1 hc2
  have hm := one_sub_ne_zero hc1 hc2
  have hZ3 : (Z1 * 2 * Z2 - x1 * y1 * Z1 * 2 * dEd * (x2 * y2 * Z2)) *
      (Z1 * 2 * Z2 + x1 * y1 * Z1 * 2 * dEd * (x2 * y2 * Z2)) ≠ 0 := by
    have h2 : (2 : ZMod p) ≠ 0 := Complete.two_ne_zero (d := dEd)
    have : (Z1 * 2 * Z2 - x1 * y1 * Z1 * 2 * dEd * (x2 * y2 * Z2)) *
        (Z1 * 2 * Z2 + x1 * y1 * Z1 * 2 * dEd * (x2 * y2 * Z2)) =
        (2 * Z1 * Z2) ^ 2 * (1 - dEd * x1 * x2 * y1 * y2) * (1 + dEd * x1 * x2 * y1 * y2) := by
      ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero h2 hZ1) hZ2)) hm) hp
  refine ⟨hZ3, by simp only [addExt]; ring, ?_⟩
  show _ = add dEd (x1, y1) (x2, y2)
  simp only [addExt, add, Prod.mk.injEq]
  constructor
  · rw [div_eq_div_iff hZ3 hp]; ring
  · rw [div_eq_div_iff hZ3 hm]; ring

/-- The reference `point_identity` is `(0, 1, 1, 0)`. -/
theorem ref_point_identity : ristretto_ref.edwards.point_identity = ok ((0, 1, 1, 0) : RefPt) := by
  simp [ristretto_ref.edwards.point_identity, field.fe_lit]

/-- `(0, 1, 1, 0)` represents the identity. -/
theorem rep_zero : Rep (0, 1, 1, 0) (0 : Point dEd) := by
  refine ⟨one_ne_zero, by ring, ?_⟩
  simp

/-- One bit of the scalar: `n mod 2^(i+1)` adds `2^i` to `n mod 2^i` if bit `i` is set. -/
theorem mod_two_pow_succ' (n i : Nat) :
    n % 2 ^ (i + 1) = n % 2 ^ i + (if n.testBit i then 2 ^ i else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> simp [h]

/-- The value of a scalar: its canonical representative, below `l`. -/
def scVal (s : scalar.Scalar) : Nat := (show ZMod scalar.l from s).val

/-- The loop of `point_mul`. Before step `i`, the register `p` represents `2^i • P` and the
accumulator `q` represents `(s mod 2^i) • P`. -/
theorem point_mul_loop_spec (s : scalar.Scalar) (P : Point dEd) :
    ∀ n, ∀ (i : Usize), i.val + n = 256 → ∀ (pp q : RefPt),
      Rep pp ((2 ^ i.val) • P) → Rep q ((scVal s % 2 ^ i.val) • P) →
      ristretto_ref.edwards.point_mul_loop s pp q i ⦃ r => Rep r ((scVal s % 2 ^ 256) • P) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i hi pp q _ hq
    rw [ristretto_ref.edwards.point_mul_loop]
    have : ¬ i < 256#usize := by scalar_tac
    rw [if_neg this, spec_ok]
    rwa [show i.val = 256 by omega] at hq
  | succ n ih =>
    intro i hi pp q hp hq
    rw [ristretto_ref.edwards.point_mul_loop]
    have hlt : i < 256#usize := by scalar_tac
    rw [if_pos hlt]
    have hp2 : Rep (addExt pp pp) ((2 ^ (i.val + 1)) • P) := by
      rw [pow_succ, mul_two, add_nsmul]
      exact addExt_rep hp hp
    have hbit := mod_two_pow_succ' (scVal s) i.val
    by_cases hb : (scVal s).testBit i.val
    · have hb' : (show ZMod scalar.l from s).val.testBit i.val = true := hb
      simp only [scalar.sc_bit, hb', bind_ok, ref_point_add, ↓reduceIte]
      step as ⟨i1, hi1⟩
      apply ih i1 (by omega) _ _ (by rw [hi1]; exact hp2)
      rw [hi1, hbit, if_pos hb, add_nsmul]
      exact addExt_rep hq hp
    · have hb' : (show ZMod scalar.l from s).val.testBit i.val = false := by simpa [scVal] using hb
      simp only [scalar.sc_bit, hb', bind_ok, ref_point_add, Bool.false_eq_true, ↓reduceIte]
      step as ⟨i1, hi1⟩
      apply ih i1 (by omega) _ _ (by rw [hi1]; exact hp2)
      rw [hi1, hbit, if_neg hb, Nat.add_zero]
      exact hq

/-- The reference `point_mul s P` computes `s • P`, where `s` is read as its canonical
representative below `l`. The input needs only to represent a point of the curve. -/
theorem point_mul_spec (s : scalar.Scalar) (Q : ExtPt) (P : Point dEd) (h : Rep Q P) :
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
value of 32 bytes, gets `(k mod l) • P`. This is `k • P` if `k < l`, or if `l • P = 0`.
`Point dEd` is the full group of the curve, of order `8 l`, so `l • P = 0` does not hold for
every point. -/

/-- With the scalar `k mod l`: the reference computes `(k mod l) • P`. -/
theorem point_mul_spec_nat (k : Nat) (s : scalar.Scalar) (hs : ((k : ZMod scalar.l)) = s)
    (Q : ExtPt) (P : Point dEd) (h : Rep Q P) :
    ristretto_ref.edwards.point_mul s Q ⦃ r => Rep r ((k % scalar.l) • P) ⦄ := by
  have hv : scVal s = k % scalar.l := by
    rw [scVal, ← ZMod.val_natCast]
    exact congrArg ZMod.val hs.symm
  rw [← hv]
  exact point_mul_spec s Q P h

/-- If `k < l`, the reference computes `k • P`. -/
theorem point_mul_spec_lt (k : Nat) (hk : k < scalar.l) (s : scalar.Scalar)
    (hs : ((k : ZMod scalar.l)) = s) (Q : ExtPt) (P : Point dEd) (h : Rep Q P) :
    ristretto_ref.edwards.point_mul s Q ⦃ r => Rep r (k • P) ⦄ := by
  have := point_mul_spec_nat k s hs Q P h
  rwa [Nat.mod_eq_of_lt hk] at this

/-- If `l • P = 0`, the reference computes `k • P` for every `k`. -/
theorem point_mul_spec_order (k : Nat) (s : scalar.Scalar) (hs : ((k : ZMod scalar.l)) = s)
    (Q : ExtPt) (P : Point dEd) (h : Rep Q P) (hP : scalar.l • P = 0) :
    ristretto_ref.edwards.point_mul s Q ⦃ r => Rep r (k • P) ⦄ := by
  have := point_mul_spec_nat k s hs Q P h
  have e : k • P = (k % scalar.l) • P := by
    conv_lhs => rw [← Nat.mod_add_div k scalar.l]
    rw [add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]
  rwa [e]

end RistrettoSim
