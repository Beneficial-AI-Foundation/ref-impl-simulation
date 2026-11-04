import Sim.LadderMath
import DalekSim.Edwards
import Mathlib.Tactic.FieldSimp

/-! # Edwards doubling and the Montgomery ladder

For `(x, y)` on `-x² + y² = 1 + d x² y²`, with `d` not a square and `121666 d = -121665`,
`u = (1 + y) / (1 - y)` maps the affine Edwards double of `(x, y)` to
`enc (dbl (1 + y, 1 - y))` (`toU_dblY`). `dadd_core` is the cleared-denominator identity
behind differential addition. Neither proof uses the Edwards group law. `dbl_key` and
`dbl_factor_ne_zero` are shared with `dbl_rep` of `Sim/EdwardsLadder.lean`.

With `a⁻¹ = 0` for `a = 0`, the identity `(0, 1)` maps to 0, as in
`EdwardsPoint::to_montgomery`. `toU_dblY` therefore has no case split. It holds for `(0, 1)`
and `(0, -1)`. -/

namespace X25519Sim.EdwardsBridge

open X25519Sim.LadderMath

variable {F : Type*} [Field F]

/-- The Montgomery u-coordinate `(1 + y) (1 - y)⁻¹` of the Edwards point with y-coordinate
`y`, as in `EdwardsPoint::to_montgomery`. -/
def toU (y : F) : F := (1 + y) * (1 - y)⁻¹

/-- The y-coordinate of `(x, y) + (x, y)` by the unified Edwards addition formula with
`a = -1`: `(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)`. -/
def dblY (d x y : F) : F := (y * y + x * x) / (1 - d * x * x * y * y)

section DblKey

variable {d x y : F} (hd' : 121666 * d = -121665) (hc : -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2)
include hd' hc

/-- `1 + d y² ≠ 0` for `(x, y)` on the curve: otherwise `y² = 1`, so `d = -1`. -/
theorem one_add_d_sq_ne_zero : 1 + d * y ^ 2 ≠ 0 := by
  intro h
  have hy : y ^ 2 = 1 := by linear_combination hc + x ^ 2 * h
  exact one_ne_zero
    (by linear_combination 121666 * h - 121666 * d * hy - hd' : (1 : F) = 0)

/-- The doubling identity `(1 + x²) (1 + 121665 (1 - y²)) = y²` for `(x, y)` on the curve. -/
theorem dbl_key : (1 + x ^ 2) * (1 + 121665 * (1 - y ^ 2)) = y ^ 2 := by
  have hx : x ^ 2 * (1 + d * y ^ 2) = y ^ 2 - 1 := by linear_combination -hc
  have : (1 + d * y ^ 2) * ((1 + x ^ 2) * (1 + 121665 * (1 - y ^ 2)) - y ^ 2) = 0 := by
    linear_combination (1 + 121665 * (1 - y ^ 2)) * hx + y ^ 2 * (1 - y ^ 2) * hd'
  linear_combination (mul_eq_zero.mp this).resolve_left (one_add_d_sq_ne_zero hd' hc)

/-- `1 + 121665 (1 - y²) ≠ 0` for `(x, y)` on the curve: otherwise `y = 0` by `dbl_key`, so
`d = -1`. -/
theorem dbl_factor_ne_zero : 1 + 121665 * (1 - y ^ 2) ≠ 0 := by
  intro h0
  have hk := dbl_key hd' hc
  rw [h0, mul_zero] at hk
  have hy0 : y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk.symm
  subst hy0
  exact one_ne_zero (by linear_combination (1 + d) * h0 - hd' : (1 : F) = 0)

end DblKey

/-- If `u (1 - y) = 1 + y` and `2 ≠ 0`, then `1 - y ≠ 0`. -/
theorem one_sub_ne_zero_of_u {u y : F} (h2 : (2 : F) ≠ 0) (hu : u * (1 - y) = 1 + y) :
    1 - y ≠ 0 := by
  intro h; apply h2; linear_combination -hu + u * h + h

/-- The u-coordinate of the Edwards double of `(x, y)` is the encoding of the ladder doubling
of `(1 + y : 1 - y)`. -/
theorem toU_dblY (d x y : F) (hd : ¬IsSquare d) (hd' : 121666 * d = -121665)
    (hc : -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2) :
    toU (dblY d x y) = enc (dbl (1 + y, 1 - y)) := by
  -- `2 ≠ 0`, because `121666 d = -121665`.
  have h2 : (2 : F) ≠ 0 := by
    intro h
    exact one_ne_zero (by linear_combination hd' - (60833 * d + 60832) * h : (1 : F) = 0)
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
  have hdy := one_add_d_sq_ne_zero hd' hc
  have hk := dbl_key hd' hc
  rw [toU, ← div_eq_mul_inv, enc, ← div_eq_mul_inv]
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
    simp [dbl, hZ, hY]
  · have hK := dbl_factor_ne_zero hd' hc
    have hL : (1 + dblY d x y) / (1 - dblY d x y) = (1 + x ^ 2) / (1 - y ^ 2) := by
      have e1 : 1 + dblY d x y = 2 * (1 + x ^ 2) / (1 - d * x * x * y * y) := by
        simp only [dblY]; rw [eq_div_iff hs, add_mul, div_mul_cancel₀ _ hs]
        linear_combination hc
      have e2 : 1 - dblY d x y = 2 * (1 - y ^ 2) / (1 - d * x * x * y * y) := by
        simp only [dblY]; rw [eq_div_iff hs, sub_mul, div_mul_cancel₀ _ hs]
        linear_combination hc
      rw [e1, e2, div_div_div_cancel_right₀ hs, mul_div_mul_left _ _ h2]
    have hR : (dbl (1 + y, 1 - y)).1 / (dbl (1 + y, 1 - y)).2 =
        y ^ 2 / ((1 - y ^ 2) * (1 + 121665 * (1 - y ^ 2))) := by
      have h16 : (16 : F) ≠ 0 := by
        rw [show (16 : F) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2
      have e : dbl (1 + y, 1 - y) =
          (16 * y ^ 2, 16 * ((1 - y ^ 2) * (1 + 121665 * (1 - y ^ 2)))) := by
        simp only [dbl, Prod.mk.injEq]; constructor <;> ring
      rw [e, mul_div_mul_left _ _ h16]
    rw [hL, hR, div_eq_div_iff hy2 (mul_ne_zero hy2 hK)]
    linear_combination (1 - y ^ 2) * hk

/-- For `(x₁, y₁)` and `(x₂, y₂)` on `-x² + y² = 1 + d x² y²`: `N₊ (y₁ - y₂)² = N₋ (y₁ + y₂)²`.
`N₊` and `N₋` are the products of the numerators and of the denominators of `(1 + y) / (1 - y)`
for `P + Q` and `P - Q` under the unified addition formula. -/
theorem dadd_core {R : Type*} [CommRing R] (d x1 y1 x2 y2 : R)
    (hc1 : -x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (hc2 : -x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2) :
    ((1 + y1 * y2) ^ 2 - (d * x1 * x2 * y1 * y2 - x1 * x2) ^ 2) * (y1 - y2) ^ 2 =
    ((1 - y1 * y2) ^ 2 - (d * x1 * x2 * y1 * y2 + x1 * x2) ^ 2) * (y1 + y2) ^ 2 := by
  linear_combination -4 * y1 * y2 * (x2 ^ 2 * (1 + d * y2 ^ 2) * hc1 + (y1 ^ 2 - 1) * hc2)

/-- `toU_dblY` on Curve25519, with no hypothesis but the curve equation. -/
theorem toU_dblY_curve25519 (x y : ZMod p)
    (hc : -x ^ 2 + y ^ 2 = 1 + DalekSim.dEd * x ^ 2 * y ^ 2) :
    toU (dblY DalekSim.dEd x y) = enc (dbl (1 + y, 1 - y)) :=
  toU_dblY DalekSim.dEd x y DalekSim.dEd_not_square DalekSim.dEd_rel hc

end X25519Sim.EdwardsBridge
