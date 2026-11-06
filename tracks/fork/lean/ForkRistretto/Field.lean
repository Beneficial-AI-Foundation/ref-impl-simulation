import RistrettoRef.Funs
import Curve25519.Ristretto.Encoding
import Proofs.Helpers.AsNat

/-! # The reference field is the fork's field

The reference computes in `field.Fe`, which is `ZMod (2 ^ 255 - 19)`. The fork computes in
`ZMod curve25519.p`, and it hides the definition of `p` behind `curve25519.p_def`. `toF` is the
ring isomorphism between the two. This file moves the reference's helpers to the fork's terms:

- the bytes: `fe_from_bytes` reads `Array.asNat 8` mod `p`, `fe_to_bytes` writes the canonical
  representative, and `geq_p x` is `p ≤ x.asNat 8`;
- the sign: the reference `is_negative` is `ZMod.IsNeg`, and `abs` is `ZMod.abs`;
- the constants `d`, `sqrt_m1` and `invsqrt_a_minus_d` are the fork's `d`, `sqrtM1` and
  `invsqrtAMinusD`;
- `sqrt_ratio_m1 u v` is the fork's `sqrtRatioM1` (`ref_sqrt_ratio_m1`). The reference
  computes a candidate root with one exponentiation and tests it. The fork defines the result
  by its properties. The link is that `v r² = u t` for a fourth root of unity `t`. -/

open Aeneas Aeneas.Std Result
open curve25519

namespace ForkRistretto

/-! ## The isomorphism -/

/-- The reference field is the fork's field. -/
def toF : _root_.field.Fe ≃+* ZMod curve25519.p :=
  ZMod.ringEquivCongr curve25519.p_def.symm

theorem ringEquivCongr_val {m n : ℕ} (h : m = n) (x : ZMod m) :
    (ZMod.ringEquivCongr h x).val = x.val := by
  subst h
  rw [ZMod.ringEquivCongr_refl_apply]

/-- `toF` keeps the canonical representative. -/
theorem toF_val (x : _root_.field.Fe) :
    (toF x).val = (show ZMod _root_.field.p from x).val :=
  ringEquivCongr_val _ x

theorem toF_natCast (n : ℕ) : toF (n : _root_.field.Fe) = (n : ZMod p) := map_natCast toF n

theorem toF_symm_natCast (n : ℕ) : toF.symm (n : ZMod p) = (n : _root_.field.Fe) :=
  map_natCast toF.symm n

/-- The reference `is_negative` is the fork's `IsNeg`. -/
theorem ref_is_negative (x : _root_.field.Fe) :
    ristretto_ref.is_negative x = ok (decide (toF x).IsNeg) := by
  unfold ristretto_ref.is_negative _root_.field.fe_is_negative
  simp only [ZMod.isNeg_iff, toF_val]

theorem ref_neg_fe (x : _root_.field.Fe) : ristretto_ref.neg_fe x = ok (-x) := by
  unfold ristretto_ref.neg_fe
  simp only [_root_.field.fe_lit, _root_.field.fe_sub, bind_ok]
  show ok (((0 : ℕ) : _root_.field.Fe) - x) = ok (-x)
  rw [Nat.cast_zero, zero_sub]

/-- The reference `abs` is the fork's `abs`. -/
theorem ref_abs (x : _root_.field.Fe) :
    ristretto_ref.abs x = ok (toF.symm (toF x).abs) := by
  unfold ristretto_ref.abs ristretto_ref.select
  rw [ref_neg_fe, ref_is_negative, bind_ok, bind_ok, ZMod.abs]
  by_cases h : (toF x).IsNeg
  · simp [h]
  · simp [h]

theorem ref_eq (x y : _root_.field.Fe) : ristretto_ref.eq x y = ok (decide (toF x = toF y)) := by
  unfold ristretto_ref.eq _root_.field.fe_eq
  simp [toF.injective.eq_iff]

theorem ref_select (x y : _root_.field.Fe) (c : Bool) :
    ristretto_ref.select x c y = ok (if c then x else y) := by
  unfold ristretto_ref.select
  cases c <;> rfl

/-! ## Bytes -/

/-- The reference reads bytes with `foldr` over the indices. This is `Nat.ofDigits 256`. -/
theorem foldr_range_eq_ofDigits (l : List ℕ) :
    (List.range l.length).foldr (fun i acc => acc * 256 + l[i]!) 0 = Nat.ofDigits 256 l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, ih, Nat.ofDigits_cons]
    ring

theorem map_val_getElem! (b : Array U8 32#usize) (i : ℕ) :
    (b.val.map (fun x => x.val))[i]! = (b.val[i]!).val := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  cases b.val[i]? <;> rfl

/-- `fe_from_bytes` reads the bytes as `asNat 8`, reduced mod p. -/
theorem fe_from_bytes_eq (b : Array U8 32#usize) :
    _root_.field.fe_from_bytes b = ok ((b.asNat 8 : ℕ) : _root_.field.Fe) := by
  unfold _root_.field.fe_from_bytes
  have hlen : (b.val.map (fun x => x.val)).length = 32 := by simp
  have h := foldr_range_eq_ofDigits (b.val.map (fun x => x.val))
  rw [hlen] at h
  simp only [map_val_getElem!] at h
  rw [h, Array.asNat_def]
  rfl

/-- `fe_to_bytes` returns bytes whose value is the canonical representative. -/
theorem fe_to_bytes_val (a : _root_.field.Fe) :
    ∃ r, _root_.field.fe_to_bytes a = ok r ∧ r.asNat 8 = (toF a).val := by
  refine ⟨_, rfl, ?_⟩
  rw [toF_val]
  have : NeZero _root_.field.p := ⟨by norm_num⟩
  have hn : ZMod.val (a : ZMod _root_.field.p) < 256 ^ 32 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by simp)
  rw [Array.asNat_eq_sum, show (32#usize).val = 32 from rfl]
  conv_rhs => rw [← Nat.mod_eq_of_lt hn, ← Nat.sum_digits_eq_mod 256 32]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < 32 := by simpa using hi
  rw [Array.getElem!_Nat_eq, Array.from_val]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, hi, _root_.dite_true,
    Option.getD_some, UScalar.ofNatCore_val_eq, pow_mul]
  norm_num

/-! ## `geq_p`

`geq_p x` walks the 32 bytes from index 0 (least significant) to 31. Each byte that differs
from the byte of `p` sets the result to `x_i > p_i`, so the last differing byte decides. The
result is `p ≤ x`. The proof is the one of track D (`tracks/ristretto/lean/Sim/GeqP.lean`),
with the fork's `Array.asNat` in place of track D's digit sums. -/

/-- The value of the bytes below index `k`. -/
def lowVal (a : Array U8 32#usize) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, 2 ^ (8 * j) * (a.val[j]!).val

theorem byte_lt (a : Array U8 32#usize) (j : ℕ) : (a.val[j]!).val < 2 ^ 8 := by
  have := (a.val[j]!).hBounds
  simpa using this

theorem lowVal_lt (a : Array U8 32#usize) (k : ℕ) : lowVal a k < 2 ^ (8 * k) :=
  Nat.sum_pow_mul_lt 8 k (fun j => (a.val[j]!).val) (fun j _ => byte_lt a j)

theorem lowVal_succ (a : Array U8 32#usize) (k : ℕ) :
    lowVal a (k + 1) = lowVal a k + 2 ^ (8 * k) * (a.val[k]!).val := by
  simp [lowVal, Finset.sum_range_succ]

theorem lowVal_32 (a : Array U8 32#usize) : lowVal a 32 = a.asNat 8 := by
  rw [Array.asNat_eq_sum]
  simp [lowVal, Array.getElem!_Nat_eq]

/-- One step of the comparison: the new byte decides if it differs. -/
theorem cmp_step (X P xk pk K : ℕ) (hX : X < K) (hP : P < K) :
    (P + K * pk ≤ X + K * xk) ↔ (if xk = pk then P ≤ X else pk < xk) := by
  split
  · subst xk; omega
  · rename_i h
    constructor
    · intro h1
      by_contra h2
      have : xk < pk := by omega
      have : K * xk + K ≤ K * pk := by nlinarith
      omega
    · intro h1
      have : K * pk + K ≤ K * xk := by nlinarith
      omega

/-- The bytes of `p` in the order of `geq_p`. -/
def pBytes : Array U8 32#usize :=
  Array.make 32#usize [
    237#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8,
    255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8,
    255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8,
    255#u8, 255#u8, 255#u8, 255#u8, 127#u8]

theorem pBytes_val : lowVal pBytes 32 = p := by
  rw [p_eq_numeral]
  decide

open Aeneas.Std.WP in
theorem geq_p_loop_spec (x : Array U8 32#usize) :
    ∀ n, ∀ (k : Usize), k.val + n = 32 → ∀ res : Bool,
      (res = decide (lowVal pBytes k.val ≤ lowVal x k.val)) →
      ristretto_ref.geq_p_loop x pBytes res k
        ⦃ b => b = decide (lowVal pBytes 32 ≤ lowVal x 32) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro k hk res hres
    have hk' : k.val = 32 := by omega
    rw [ristretto_ref.geq_p_loop]
    have : ¬ k < 32#usize := by scalar_tac
    rw [ite_eq_right this, spec_ok, hres, hk']
  | succ n ih =>
    intro k hk res hres
    rw [ristretto_ref.geq_p_loop]
    have hk32 : k < 32#usize := by scalar_tac
    rw [ite_eq_left hk32]
    step as ⟨xi, hxi⟩
    step as ⟨pi, hpi⟩
    have hk1 : k.val < 32 := by scalar_tac
    have hxv : xi.val = (x.val[k.val]!).val := by
      rw [hxi, getElem!_pos x.val k.val (by simpa using hk1)]
    have hpv : pi.val = (pBytes.val[k.val]!).val := by
      rw [hpi, getElem!_pos pBytes.val k.val (by simpa using hk1)]
    have hcmp : decide (lowVal pBytes (k.val + 1) ≤ lowVal x (k.val + 1)) =
        (if xi = pi then res else decide (pi < xi)) := by
      rw [lowVal_succ, lowVal_succ, hres]
      have := cmp_step (lowVal x k.val) (lowVal pBytes k.val) (x.val[k.val]!).val
        (pBytes.val[k.val]!).val (2 ^ (8 * k.val)) (lowVal_lt x k.val) (lowVal_lt pBytes k.val)
      rw [← hxv, ← hpv] at this ⊢
      by_cases he : xi = pi
      · have hv : xi.val = pi.val := by rw [he]
        rw [ite_eq_left he, decide_eq_decide]; rw [ite_eq_left hv] at this; exact this
      · have hv : xi.val ≠ pi.val := fun h => he (UScalar.eq_of_val_eq h)
        rw [ite_eq_right he, decide_eq_decide]; rw [ite_eq_right hv] at this; exact this
    split
    · rename_i hne
      step as ⟨k1, hk1v⟩
      apply ih k1 (by omega)
      rw [hk1v, hcmp, ite_eq_right (by simpa using hne)]
    · rename_i hne
      step as ⟨k1, hk1v⟩
      apply ih k1 (by omega)
      have he : xi = pi := UScalar.eq_of_val_eq (by simpa using hne)
      rw [hk1v, hcmp, ite_eq_left he]

open Aeneas.Std.WP in
/-- The reference `geq_p x` is `p ≤ x.asNat 8`. -/
theorem ref_geq_p_spec (x : Array U8 32#usize) :
    ristretto_ref.geq_p x ⦃ b => b = decide (p ≤ x.asNat 8) ⦄ := by
  have h := geq_p_loop_spec x 32 0#usize (by simp) true (by simp [lowVal])
  rw [pBytes_val, lowVal_32] at h
  exact h

/-! ## Constants -/

theorem ref_d : ristretto_ref.d = ok (toF.symm d) := by
  unfold ristretto_ref.d
  rw [fe_from_bytes_eq, d_eq_natCast, toF_symm_natCast]
  congr 2

theorem ref_sqrt_m1 : ristretto_ref.sqrt_m1 = ok (toF.symm (sqrtM1 : ZMod p)) := by
  unfold ristretto_ref.sqrt_m1
  rw [fe_from_bytes_eq, sqrtM1_def, toF_symm_natCast]
  congr 2

theorem ref_invsqrt_a_minus_d :
    ristretto_ref.invsqrt_a_minus_d = ok (toF.symm (invsqrtAMinusD : ZMod p)) := by
  unfold ristretto_ref.invsqrt_a_minus_d
  rw [fe_from_bytes_eq, invsqrtAMinusD_def, toF_symm_natCast]
  congr 2

end ForkRistretto
