import ForkRistretto.Field

/-! # The reference `sqrt_ratio_m1` is the fork's `sqrtRatioM1`

The reference computes `r = (u v³) (u v⁷)^((p-5)/8)` and the test value `v r²`. With
`w = u v⁷`, `v r² = u t` for `t = w^((p-1)/4)`, and `t⁴ = 1`, so `t` is `1`, `-1`, `√-1` or
`-√-1`. In each case the reference result meets the characterization of the fork's
`sqrtRatioM1` (`sqrtRatioM1_eq_of_mul_sq_eq` and `sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul`).
The cases `u = 0` and `v = 0` give `r = 0`. -/

open Aeneas Aeneas.Std Result
open curve25519

namespace ForkRistretto

/-- The candidate root of the reference, in the fork's field. -/
def candR (u v : ZMod p) : ZMod p := u * (v ^ 2 * v) * (u * ((v ^ 2 * v) ^ 2 * v)) ^ _root_.field.p58

/-- `2 p58 + 1 = (p - 1) / 4`, and `4 ((p - 1) / 4) = p - 1`. -/
theorem p58_exp : 4 * (2 * _root_.field.p58 + 1) = p - 1 := by
  unfold _root_.field.p58
  rw [p_def]
  norm_num

/-- `v r² = u w^(2 p58 + 1)` with `w = u v⁷`. -/
theorem check_eq (u v : ZMod p) :
    v * candR u v ^ 2 = u * (u * ((v ^ 2 * v) ^ 2 * v)) ^ (2 * _root_.field.p58 + 1) := by
  unfold candR
  ring

theorem sqrtM1_ne_one : (sqrtM1 : ZMod p) ≠ 1 := by
  intro h
  have := sqrtM1_sq
  rw [h, one_pow] at this
  exact (two_ne_zero : (2 : ZMod p) ≠ 0) (by linear_combination this)

theorem sqrtM1_ne_neg_one : (sqrtM1 : ZMod p) ≠ -1 := by
  intro h
  have := sqrtM1_sq
  rw [h] at this
  exact (two_ne_zero : (2 : ZMod p) ≠ 0) (by linear_combination this)

/-- In `ZMod p`, `2 x = 0` implies `x = 0`. -/
theorem eq_zero_of_two_mul {x : ZMod p} (h : 2 * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- A fourth root of unity is `1`, `-1`, `√-1` or `-√-1`. -/
theorem fourth_root {t : ZMod p} (h : t ^ 4 = 1) :
    t = 1 ∨ t = -1 ∨ t = sqrtM1 ∨ t = -sqrtM1 := by
  have hi := sqrtM1_sq
  have h0 : (t - 1) * (t + 1) * ((t - sqrtM1) * (t + sqrtM1)) = 0 := by
    linear_combination h + (1 - t ^ 2) * hi
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h2))
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h2)))
    · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h2)))

/-- The result of the reference, as a function of the test value `c = v r²`. -/
def refResult (u r c : ZMod p) : Bool × ZMod p :=
  (decide (c = u) || decide (c = -u),
    (if c = -u ∨ c = -u * sqrtM1 then (sqrtM1 : ZMod p) * r else r).abs)

/-- The reference computation is `sqrtRatioM1`. -/
theorem refResult_eq (u v : ZMod p) :
    refResult u (candR u v) (v * candR u v ^ 2) = sqrtRatioM1 u v := by
  have hi := sqrtM1_sq
  have hi0 := sqrtM1_ne_zero
  have hi1 := sqrtM1_ne_one
  have hin := sqrtM1_ne_neg_one
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero
  by_cases hu : u = 0
  · subst hu
    rw [sqrtRatioM1_zero_left]
    simp [refResult, candR, ZMod.abs_zero]
  by_cases hv : v = 0
  · subst hv
    rw [sqrtRatioM1_zero_right hu]
    have hr : candR u 0 = 0 := by simp [candR]
    have hnu : (0 : ZMod p) ≠ -u := fun h => hu (neg_eq_zero.mp h.symm)
    simp [refResult, hr, Ne.symm hu, hnu, ZMod.abs_zero]
  have hw0 : u * ((v ^ 2 * v) ^ 2 * v) ≠ 0 := mul_ne_zero hu (by simp [hv])
  have ht4 : ((u * ((v ^ 2 * v) ^ 2 * v)) ^ (2 * _root_.field.p58 + 1)) ^ 4 = 1 := by
    rw [← pow_mul, show (2 * _root_.field.p58 + 1) * 4 = p - 1 by rw [Nat.mul_comm]; exact p58_exp]
    exact ZMod.pow_card_sub_one_eq_one hw0
  have hc := check_eq u v
  generalize (u * ((v ^ 2 * v) ^ 2 * v)) ^ (2 * _root_.field.p58 + 1) = t at hc ht4
  unfold refResult
  generalize candR u v = r at hc ⊢
  rw [hc]
  rcases fourth_root ht4 with rfl | rfl | rfl | rfl
  · -- `t = 1`: the root of `u / v`
    have e1 : ¬ (u * 1 = -u ∨ u * 1 = -u * sqrtM1) := by
      rintro (h' | h')
      · exact hu (eq_zero_of_two_mul (by linear_combination h'))
      · exact hin (mul_left_cancel₀ hu (by linear_combination h'))
    rw [ite_eq_right e1, sqrtRatioM1_eq_of_mul_sq_eq (r := r.abs) hv (by rw [ZMod.abs_sq]; linear_combination hc)
      (ZMod.not_isNeg_abs r)]
    simp
  · -- `t = -1`: the root of `u / v` times `√-1`
    have e1 : u * -1 = -u ∨ u * -1 = -u * sqrtM1 := Or.inl (by ring)
    have e2 : u * -1 ≠ u := fun h' => hu (eq_zero_of_two_mul (by linear_combination -h'))
    rw [ite_eq_left e1, sqrtRatioM1_eq_of_mul_sq_eq (r := ((sqrtM1 : ZMod p) * r).abs) hv
      (by rw [ZMod.abs_sq]; linear_combination (v * r ^ 2) * hi - hc)
      (ZMod.not_isNeg_abs _)]
    simp
  · -- `t = √-1`: not a square, the root of `√-1 u / v`
    have e1 : ¬ (u * sqrtM1 = -u ∨ u * sqrtM1 = -u * sqrtM1) := by
      rintro (h' | h')
      · exact hin (mul_left_cancel₀ hu (by linear_combination h'))
      · exact mul_ne_zero hu hi0 (eq_zero_of_two_mul (by linear_combination h'))
    have e2 : u * sqrtM1 ≠ u := fun h' => hi1 (mul_left_cancel₀ hu (by linear_combination h'))
    have e3 : u * sqrtM1 ≠ -u := fun h' => hin (mul_left_cancel₀ hu (by linear_combination h'))
    rw [ite_eq_right e1, sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul (r := r.abs) hu hv
      (by rw [ZMod.abs_sq]; linear_combination hc) (ZMod.not_isNeg_abs r)]
    simp [e2, e3]
  · -- `t = -√-1`: not a square, `√-1 r` is the root of `√-1 u / v`
    have e1 : u * -sqrtM1 = -u ∨ u * -sqrtM1 = -u * sqrtM1 := Or.inr (by ring)
    have e2 : u * -(sqrtM1 : ZMod p) ≠ u := fun h' =>
      hin (mul_left_cancel₀ hu (by linear_combination -h'))
    have e3 : u * -(sqrtM1 : ZMod p) ≠ -u := fun h' =>
      hi1 (mul_left_cancel₀ hu (by linear_combination -h'))
    rw [ite_eq_left e1, sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul (r := ((sqrtM1 : ZMod p) * r).abs) hu hv
      (by rw [ZMod.abs_sq]; linear_combination (v * r ^ 2) * hi - hc)
      (ZMod.not_isNeg_abs _)]
    simp only [e2, e3, decide_false, Bool.or_false]

/-- The reference `sqrt_ratio_m1` is the fork's `sqrtRatioM1`. -/
theorem ref_sqrt_ratio_m1 (U V : _root_.field.Fe) :
    ristretto_ref.sqrt_ratio_m1 U V =
      ok ((sqrtRatioM1 (toF U) (toF V)).1, toF.symm (sqrtRatioM1 (toF U) (toF V)).2) := by
  rw [← refResult_eq]
  unfold ristretto_ref.sqrt_ratio_m1
  simp only [_root_.field.fe_sq, _root_.field.fe_mul, _root_.field.fe_pow_p58, ref_eq, ref_neg_fe,
    ref_sqrt_m1, ref_select, ref_abs, bind_ok, map_mul, map_pow, map_neg,
    RingEquiv.apply_symm_apply]
  unfold refResult candR
  generalize toF V * (toF U * (toF V ^ 2 * toF V) *
    (toF U * ((toF V ^ 2 * toF V) ^ 2 * toF V)) ^ _root_.field.p58) ^ 2 = c
  by_cases h1 : c = -toF U <;> by_cases h2 : c = -toF U * sqrtM1 <;> by_cases h3 : c = toF U <;>
    (try simp only [eq_true h1]) <;> (try simp only [eq_false h1]) <;>
    (try simp only [eq_true h2]) <;> (try simp only [eq_false h2]) <;>
    (try simp only [eq_true h3]) <;> (try simp only [eq_false h3]) <;>
    simp [apply_ite toF]

end ForkRistretto
