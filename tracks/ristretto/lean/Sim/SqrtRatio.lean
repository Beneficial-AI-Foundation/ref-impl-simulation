import Sim.Choice
import Sim.Consts

/-! # `sqrt_ratio_i` against the reference `sqrt_ratio_m1`

Both compute `r = (u v³) (u v⁷)^((p-5)/8)`, test `v r²` against `u`, `-u` and `-u √-1`,
multiply `r` by `√-1` on the two flipped cases and take the nonnegative root. The proof goes
call by call. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace RistrettoSim

open DalekSim

/-- `bitor` on choices. -/
theorem bitor_eq (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b =
      ok (if a.val = 1#u8 ∨ b.val = 1#u8 then cOne else cZero) := by
  unfold subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  split <;> rfl

theorem cOne_val : cOne.val = 1#u8 := rfl
theorem cZero_val : cZero.val = 0#u8 := rfl

/-- The canonical representative is odd. A named predicate, so that rewrites do not unfold
the modulus. -/
def negP (x : _root_.field.Fe) : Prop := (show ZMod _root_.field.p from x).val % 2 = 1

instance (x : _root_.field.Fe) : Decidable (negP x) :=
  inferInstanceAs (Decidable ((show ZMod _root_.field.p from x).val % 2 = 1))

/-- The reference `is_negative` tests `negP`. -/
theorem ref_is_negative (x : _root_.field.Fe) :
    ristretto_ref.is_negative x = ok (decide (negP x)) := rfl

/-- `fe(0) - x = -x`. -/
theorem ref_zero_sub (x : _root_.field.Fe) :
    ((((0#u32 : U32) : Nat) : _root_.field.Fe)) - x = -x := by
  show (((0 : Nat) : _root_.field.Fe)) - x = -x
  rw [Nat.cast_zero, zero_sub]

/-- The nonnegative choice of `x` and `-x`. -/
def absZ (x : _root_.field.Fe) : _root_.field.Fe :=
  if negP x then -x else x

/-- The reference `abs` is `absZ`. -/
theorem ref_abs (x : _root_.field.Fe) :
    ristretto_ref.abs x = ok (absZ x) := by
  unfold ristretto_ref.abs ristretto_ref.select ristretto_ref.neg_fe ristretto_ref.is_negative
  simp only [_root_.field.fe_sub, _root_.field.fe_lit, _root_.field.fe_is_negative, bind_ok]
  unfold absZ negP
  by_cases h : (show ZMod _root_.field.p from x).val % 2 = 1
  · simp only [h, decide_true, if_true, ref_zero_sub]
  · simp only [h, decide_false, if_false, Bool.false_eq_true]

/-- The candidate root of `sqrt_ratio_m1`: `(u v³) (u v⁷)^((p-5)/8)`. -/
def refR (U V : _root_.field.Fe) : _root_.field.Fe :=
  U * (V ^ 2 * V) * (U * ((V ^ 2 * V) ^ 2 * V)) ^ _root_.field.p58

/-- The test value `v r²`. -/
def refChk (U V : _root_.field.Fe) : _root_.field.Fe := V * refR U V ^ 2

/-- `√-1` in the reference field. -/
def zI : _root_.field.Fe := ((nSqrtM1 : Nat) : _root_.field.Fe)

/-- The control flow of `sqrt_ratio_m1` after the field operations. -/
theorem sqrt_ratio_tail (C U I R : _root_.field.Fe) :
    (do
      let f ← if decide (C = -U) = true then ok true else ok (decide (C = -U * I))
      let r1 ← if f = true then ok (I * R) else ok R
      if decide (C = U) = true then ok (true, absZ r1) else ok (decide (C = -U), absZ r1)) =
    (ok (decide (C = U) || decide (C = -U), absZ (if C = -U ∨ C = -U * I then I * R else R)) :
      Result (Bool × _root_.field.Fe)) := by
  by_cases h1 : C = U <;> by_cases h2 : C = -U <;> by_cases h3 : C = -U * I <;>
    simp_all

/-- The real exponent `(p - 5) / 8` is the reference exponent. -/
theorem p58_eq : (p - 5) / 8 = _root_.field.p58 := by
  unfold _root_.field.p58 p; rfl

/-- hacspec computes the exponent of `sqrt_ratio_m1` as `(P() - fe(5)) / fe(8)` in the field,
where `P()` is 0. Its value is `-5 / 8`. The field model uses the natural number `p58`. This
lemma shows that `p58` is `-5 / 8` in `ZMod p`, so the two exponents agree. -/
theorem p58_field : ((_root_.field.p58 : Nat) : _root_.field.Fe) * 8 = -5 := by
  unfold _root_.field.p58
  decide

/-- The reference `sqrt_ratio_m1` in closed form. -/
theorem ref_sqrt_ratio_eq (U V : _root_.field.Fe) :
    ristretto_ref.sqrt_ratio_m1 U V =
      ok (decide (refChk U V = U) || decide (refChk U V = -U),
        absZ (if refChk U V = -U ∨ refChk U V = -U * zI then zI * refR U V else refR U V)) := by
  unfold ristretto_ref.sqrt_ratio_m1 ristretto_ref.eq ristretto_ref.neg_fe ristretto_ref.select
  simp only [_root_.field.fe_sq, _root_.field.fe_mul, _root_.field.fe_sub, _root_.field.fe_lit,
    _root_.field.fe_eq, _root_.field.fe_pow_p58, ref_sqrt_m1, ref_abs, bind_ok]
  simp only [ref_zero_sub]
  exact sqrt_ratio_tail _ _ _ _

/-- If the limbs of `u` and `v` are below `2 ^ 54`, `sqrt_ratio_i u v` returns without
failure. The reference `sqrt_ratio_m1 (toZ u) (toZ v)` returns `(b, toZ r.2)`, where `b` is
true iff the real `Choice` `r.1` is 1. The limbs of `r.2` are below `2 ^ 52`. -/
theorem sqrt_ratio_i_refines (u v : FE) (hu : Bnd 54 u) (hv : Bnd 54 v) :
    field.FieldElement51.sqrt_ratio_i u v ⦃ r =>
      ∃ b, ristretto_ref.sqrt_ratio_m1 (toZ u) (toZ v) = ok (b, toZ r.2) ∧
        (b = true ↔ r.1.val = 1#u8) ∧ Bnd 52 r.2 ⦄ := by
  unfold field.FieldElement51.sqrt_ratio_i
  step with square_z as ⟨fe, hfe, bfe⟩
  step with mul_z as ⟨v3, hv3, bv3⟩
  · exact bnd_mono bfe (by norm_num)
  step with square_z as ⟨fe1, hfe1, bfe1⟩
  · exact bnd_mono bv3 (by norm_num)
  step with mul_z as ⟨v7, hv7, bv7⟩
  · exact bnd_mono bfe1 (by norm_num)
  step with mul_z as ⟨fe2, hfe2, bfe2⟩
  · exact bnd_mono bv3 (by norm_num)
  step with mul_z as ⟨fe3, hfe3, bfe3⟩
  · exact bnd_mono bv7 (by norm_num)
  step with pow_p58_z as ⟨fe4, hfe4, bfe4⟩
  · exact bnd_mono bfe3 (by norm_num)
  step with mul_z as ⟨r, hr, br⟩
  · exact bnd_mono bfe2 (by norm_num)
  · exact bnd_mono bfe4 (by norm_num)
  step with square_z as ⟨fe5, hfe5, bfe5⟩
  · exact bnd_mono br (by norm_num)
  step with mul_z as ⟨check, hcheck, bcheck⟩
  · exact bnd_mono bfe5 (by norm_num)
  step with sqrt_m1_spec as ⟨fe6, hfe6, bfe6⟩
  step with ct_eq_z as ⟨c1, hc1⟩
  step with neg_z as ⟨fe7, hfe7, bfe7⟩
  step with ct_eq_z as ⟨c2, hc2⟩
  step with mul_z as ⟨fe8, hfe8, bfe8⟩
  · exact bnd_mono bfe7 (by norm_num)
  · exact bnd_mono bfe6 (by norm_num)
  step with ct_eq_z as ⟨c3, hc3⟩
  step with mul_z as ⟨r_prime, hrp, brp⟩
  · exact bnd_mono bfe6 (by norm_num)
  · exact bnd_mono br (by norm_num)
  rw [bitor_eq, bind_ok]
  step with conditional_assign_eq as ⟨r1, hr1⟩
  step with is_negative_z as ⟨cn, hcn⟩
  have br1 : Bnd 52 r1 := by rw [hr1]; split <;> assumption
  step with neg_z as ⟨r_neg, hrn, brn⟩
  · exact bnd_mono br1 (by norm_num)
  step with conditional_assign_eq as ⟨r2, hr2⟩
  rw [bitor_eq, bind_ok, spec_ok]
  -- the values of the real computation, in the reference's terms
  have hR : toZ r = refR (toZ u) (toZ v) := by
    rw [hr, hfe2, hfe4, hfe3, hv7, hfe1, hv3, hfe, p58_eq]; rfl
  have hC : toZ check = refChk (toZ u) (toZ v) := by
    rw [hcheck, hfe5, hR]; rfl
  have hI : toZ fe6 = zI := hfe6
  have e1 : c1.val = 1#u8 ↔ refChk (toZ u) (toZ v) = toZ u := by rw [hc1, hC]
  have e2 : c2.val = 1#u8 ↔ refChk (toZ u) (toZ v) = - toZ u := by rw [hc2, hC, hfe7]
  have e3 : c3.val = 1#u8 ↔ refChk (toZ u) (toZ v) = - toZ u * zI := by
    rw [hc3, hC, hfe8, hfe7, hI]
  have hsel : ∀ a b : subtle.Choice,
      (if a.val = 1#u8 ∨ b.val = 1#u8 then cOne else cZero).val = 1#u8 ↔
        (a.val = 1#u8 ∨ b.val = 1#u8) := by
    intro a b; split <;> simp_all [cOne_val, cZero_val]
  have hr1z : toZ r1 = if refChk (toZ u) (toZ v) = - toZ u ∨
      refChk (toZ u) (toZ v) = - toZ u * zI then zI * refR (toZ u) (toZ v)
      else refR (toZ u) (toZ v) := by
    by_cases hc : c2.val = 1#u8 ∨ c3.val = 1#u8
    · rw [hr1, if_pos ((hsel _ _).mpr hc), hrp, hI, hR, if_pos ((or_congr e2 e3).mp hc)]
    · rw [hr1, if_neg (fun h => hc ((hsel _ _).mp h)), hR,
        if_neg (fun h => hc ((or_congr e2 e3).mpr h))]
  have hr2z : toZ r2 = absZ (toZ r1) := by
    rw [hr2]; unfold absZ negP
    by_cases hn : cn.val = 1#u8
    · rw [if_pos hn, hrn, if_pos (hcn.mp hn)]
    · rw [if_neg hn, if_neg (fun h => hn (hcn.mpr h))]
  refine ⟨_, by rw [ref_sqrt_ratio_eq, hr2z, hr1z], ?_, ?_⟩
  · rw [hsel, e1, e2]; simp
  · show Bnd 52 r2
    rw [hr2]; split <;> assumption

end RistrettoSim
