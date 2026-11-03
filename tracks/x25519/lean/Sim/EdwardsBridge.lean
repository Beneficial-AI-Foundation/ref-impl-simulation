import Sim.LadderMath
import Curve25519Dalek.Math.PrimeCerts
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! # From Edwards to Montgomery form: doubling and differential addition

A first step toward a proof of public-key derivation (`PublicKey::from`), which no theorem
of this track covers yet. dalek computes the public key on the Edwards curve `-x² + y² = 1 + d x² y²` and maps the result to the Montgomery u-coordinate
`u = (1 + y) / (1 - y)` (`EdwardsPoint::to_montgomery`). The reference computes it with the
Montgomery ladder. This file proves one step of the bridge, directly from the curve equation:
the u-coordinate of `P + P`, with `P + P` from the unified Edwards addition formula, is the
encoding of the ladder doubling `dbl` (`Sim/LadderMath.lean`) of the projective point
`(1 + y : 1 - y)` (`toU_dblY`). `dadd_core` is the polynomial identity behind the
differential addition. Neither lemma uses the Edwards group law.

The statement uses the division of Lean, with `a / 0 = 0`. So the identity `(0, 1)` has the
u-coordinate 0, as in `to_montgomery`, and the encoding of a point with `z = 0` is 0, as in
the reference. The statement has no case split: it also holds for the identity and for the
point `(0, -1)` of order 2.

The field is arbitrary. The hypotheses are those of a complete Edwards curve: `2 ≠ 0`, `-1` is
a square and `d` is not. The relation `121666 d = -121665` ties `d` to the constant 121665 of
the ladder (`A = 486662`, `(A - 2) / 4 = 121665`). Curve25519 satisfies all of them
(`toU_dblY_curve25519`). -/

namespace X25519Sim.EdwardsBridge

open X25519Sim.LadderMath

variable {F : Type*} [Field F]

/-- The Montgomery u-coordinate of the Edwards point with y-coordinate `y`. -/
def toU (y : F) : F := (1 + y) / (1 - y)

/-- The y-coordinate of `(x, y) + (x, y)` by the unified Edwards addition formula with
`a = -1`: `(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)`. -/
def dblY (d x y : F) : F := (y * y + x * x) / (1 - d * x * x * y * y)

/-- The encoding of a projective point `(x : z)`: `x / z`. -/
def enc (P : Pt F) : F := P.1 / P.2

/-- The u-coordinate of the Edwards double of `(x, y)` is the encoding of the ladder doubling
of `(1 + y : 1 - y)`. -/
theorem toU_dblY (d x y : F) (h2 : (2 : F) ≠ 0) (hi : IsSquare (-1 : F)) (hd : ¬IsSquare d)
    (hd' : 121666 * d = -121665) (hc : -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2) :
    toU (dblY d x y) = enc (dbl (1 + y, 1 - y)) := by
  -- The curve equation, solved for the part with `x`.
  have hx : x ^ 2 * (1 + d * y ^ 2) = y ^ 2 - 1 := by linear_combination -hc
  -- The denominator of the addition formula is not 0, because `d` is not a square.
  have hs : 1 - d * x * x * y * y ≠ 0 := by
    intro h
    have hx0 : x ≠ 0 := by rintro rfl; simp at h
    have hy0 : y ≠ 0 := by rintro rfl; simp at h
    refine hd ⟨(x * y)⁻¹, ?_⟩
    field_simp
    linear_combination -h
  -- `1 + d y² ≠ 0`, because `-1` is a square and `d` is not.
  have hdy : 1 + d * y ^ 2 ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hi
    have hy0 : y ≠ 0 := by rintro rfl; simp at h
    refine hd ⟨i / y, ?_⟩
    field_simp
    linear_combination h + hi
  -- The key identity: `(1 + x²) (1 + 121665 (1 - y²)) = y²`.
  have hk : (1 + x ^ 2) * (1 + 121665 * (1 - y ^ 2)) = y ^ 2 := by
    have : (1 + d * y ^ 2) * ((1 + x ^ 2) * (1 + 121665 * (1 - y ^ 2)) - y ^ 2) = 0 := by
      linear_combination (1 + 121665 * (1 - y ^ 2)) * hx + y ^ 2 * (1 - y ^ 2) * hd'
    linear_combination (mul_eq_zero.mp this).resolve_left hdy
  by_cases hy2 : 1 - y ^ 2 = 0
  · -- `y = ±1` and `x = 0`: both sides are 0.
    have hx0 : x = 0 := by
      have : x ^ 2 * (1 + d * y ^ 2) = 0 := by linear_combination hx - hy2
      simpa using (mul_eq_zero.mp this).resolve_right hdy
    subst hx0
    have hZ : ((1 : F) + 1) ^ 2 - (y + y) * (y + y) = 0 := by
      linear_combination 4 * hy2
    have hY : dblY d 0 y = 1 := by
      simp only [dblY]; rw [div_eq_one_iff_eq (by simp)]; linear_combination -hy2
    simp [enc, dbl, hZ, hY, toU]
  · have hK : 1 + 121665 * (1 - y ^ 2) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hk
      have hy0 : y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk.symm
      subst hy0
      have h1 : (1 : F) = 0 := by linear_combination (1 + d) * h0 - hd'
      exact one_ne_zero h1
    have hL : toU (dblY d x y) = (1 + x ^ 2) / (1 - y ^ 2) := by
      have e1 : 1 + dblY d x y = 2 * (1 + x ^ 2) / (1 - d * x * x * y * y) := by
        simp only [dblY]; rw [eq_div_iff hs, add_mul, div_mul_cancel₀ _ hs]
        linear_combination hc
      have e2 : 1 - dblY d x y = 2 * (1 - y ^ 2) / (1 - d * x * x * y * y) := by
        simp only [dblY]; rw [eq_div_iff hs, sub_mul, div_mul_cancel₀ _ hs]
        linear_combination hc
      rw [toU, e1, e2, div_div_div_cancel_right₀ hs, mul_div_mul_left _ _ h2]
    have hR : enc (dbl (1 + y, 1 - y)) = y ^ 2 / ((1 - y ^ 2) * (1 + 121665 * (1 - y ^ 2))) := by
      simp only [enc, dbl]
      rw [div_eq_div_iff ?_ (mul_ne_zero hy2 hK)]
      · ring
      · have : (4 : F) ≠ 0 := by
          have : (4 : F) = 2 * 2 := by norm_num
          rw [this]; exact mul_ne_zero h2 h2
        refine mul_ne_zero ?_ ?_
        · intro h
          exact hy2 ((mul_eq_zero.mp (show (4 : F) * (1 - y ^ 2) = 0 by
            linear_combination h)).resolve_left this)
        · intro h
          exact hK ((mul_eq_zero.mp (show (4 : F) * (1 + 121665 * (1 - y ^ 2)) = 0 by
            linear_combination h)).resolve_left this)
    rw [hL, hR, div_eq_div_iff hy2 (mul_ne_zero hy2 hK)]
    linear_combination (1 - y ^ 2) * hk

/-- The core identity of differential addition. For `P = (x₁, y₁)` and `Q = (x₂, y₂)` on the
curve, write `P + Q` and `P - Q` with the unified formula. Then the numerators and denominators
of `(1 + y) / (1 - y)` for `P + Q` and `P - Q` satisfy
`u(P + Q) u(P - Q) = ((y₁ + y₂) / (y₁ - y₂))²`, with the denominators multiplied out. The
right side is `((u_P u_Q - 1) / (u_P - u_Q))²`, the ladder's differential addition. The cases
with a zero denominator are not covered. -/
theorem dadd_core (d x1 y1 x2 y2 : F) (hdy1 : 1 + d * y1 ^ 2 ≠ 0) (hdy2 : 1 + d * y2 ^ 2 ≠ 0)
    (hc1 : -x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (hc2 : -x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2) :
    ((1 + y1 * y2) ^ 2 - (d * x1 * x2 * y1 * y2 - x1 * x2) ^ 2) * (y1 - y2) ^ 2 =
    ((1 - y1 * y2) ^ 2 - (d * x1 * x2 * y1 * y2 + x1 * x2) ^ 2) * (y1 + y2) ^ 2 := by
  have ha : x1 ^ 2 * (1 + d * y1 ^ 2) = y1 ^ 2 - 1 := by linear_combination -hc1
  have hb : x2 ^ 2 * (1 + d * y2 ^ 2) = y2 ^ 2 - 1 := by linear_combination -hc2
  -- Both sides depend on `x₁` and `x₂` only through `x₁² x₂²`. Multiply by the two factors
  -- `1 + d yᵢ²` and replace `xᵢ² (1 + d yᵢ²)` by `yᵢ² - 1`.
  have key : (1 + d * y1 ^ 2) * (1 + d * y2 ^ 2) *
      (((1 + y1 * y2) ^ 2 - (d * x1 * x2 * y1 * y2 - x1 * x2) ^ 2) * (y1 - y2) ^ 2 -
       ((1 - y1 * y2) ^ 2 - (d * x1 * x2 * y1 * y2 + x1 * x2) ^ 2) * (y1 + y2) ^ 2) = 0 := by
    linear_combination
      (-(d * y1 * y2 - 1) ^ 2 * (y1 - y2) ^ 2 + (d * y1 * y2 + 1) ^ 2 * (y1 + y2) ^ 2) *
        (x2 ^ 2 * (1 + d * y2 ^ 2) * ha + (y1 ^ 2 - 1) * hb)
  linear_combination (mul_eq_zero.mp key).resolve_left (mul_ne_zero hdy1 hdy2)

section Curve25519

instance : Fact (Nat.Prime (2 ^ 255 - 19)) := ⟨PrimeCert.prime_p⟩

/-- The Edwards parameter `d = -121665 / 121666` of Curve25519. -/
def dEd : ZMod (2 ^ 255 - 19) :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

theorem dEd_not_square : ¬IsSquare dEd := by
  apply (legendreSym.eq_neg_one_iff' (2 ^ 255 - 19)).mp
  norm_num [dEd]

theorem dEd_rel : 121666 * dEd = -121665 := by decide +kernel

/-- `toU_dblY` on Curve25519, with no hypothesis but the curve equation. -/
theorem toU_dblY_curve25519 (x y : ZMod (2 ^ 255 - 19))
    (hc : -x ^ 2 + y ^ 2 = 1 + dEd * x ^ 2 * y ^ 2) :
    toU (dblY dEd x y) = enc (dbl (1 + y, 1 - y)) :=
  toU_dblY dEd x y (by decide +kernel) (ZMod.exists_sq_eq_neg_one_iff.mpr (by decide))
    dEd_not_square dEd_rel hc

end Curve25519

/--
info: 'X25519Sim.EdwardsBridge.toU_dblY' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toU_dblY

/--
info: 'X25519Sim.EdwardsBridge.toU_dblY_curve25519' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toU_dblY_curve25519

/--
info: 'X25519Sim.EdwardsBridge.dadd_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dadd_core

end X25519Sim.EdwardsBridge
