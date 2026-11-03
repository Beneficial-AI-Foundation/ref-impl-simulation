import Sim.Bytes

/-! # The reference `geq_p` loop

`geq_p x` walks the 32 bytes from index 0 (least significant) to 31. Each byte that differs
from the byte of `p` sets the result to `x_i > p_i`, so the last differing byte decides. The
result is `p ≤ x`. -/

open Aeneas Aeneas.Std Result

namespace RistrettoSim

open Aeneas.Std.WP in
/-- A total-correctness triple on a `Result` gives the value it returns. -/
theorem eq_ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ v => P v ⦄) :
    ∃ v, m = ok v ∧ P v := by
  cases m using Result.cases with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact absurd h (by simp [spec_vis])
  | div => exact absurd h (by simp [spec_div])

/-- The value of the bytes below index `k`. -/
def lowVal (a : Array U8 32#usize) (k : Nat) : Nat :=
  ∑ j ∈ Finset.range k, 256 ^ j * (a.val[j]!).val

theorem lowVal_lt (a : Array U8 32#usize) (k : Nat) : lowVal a k < 256 ^ k :=
  digits_lt (fun j => (a.val[j]!).val) (byte_lt a) k

theorem lowVal_succ (a : Array U8 32#usize) (k : Nat) :
    lowVal a (k + 1) = lowVal a k + 256 ^ k * (a.val[k]!).val := by
  simp [lowVal, Finset.sum_range_succ]

/-- One step of the comparison: the new byte decides if it differs. -/
theorem cmp_step (X P xk pk K : Nat) (hX : X < K) (hP : P < K) :
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

theorem pBytes_val : lowVal pBytes 32 = 2 ^ 255 - 19 := by
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
    rw [if_neg this, spec_ok, hres, hk']
  | succ n ih =>
    intro k hk res hres
    rw [ristretto_ref.geq_p_loop]
    have hk32 : k < 32#usize := by scalar_tac
    rw [if_pos hk32]
    step as ⟨xi, hxi⟩
    step as ⟨pi, hpi⟩
    have hk1 : k.val < 32 := by scalar_tac
    have hxv : xi.val = (x.val[k.val]!).val := by rw [hxi, getElem!_pos x.val k.val (by simpa using hk1)]
    have hpv : pi.val = (pBytes.val[k.val]!).val := by
      rw [hpi, getElem!_pos pBytes.val k.val (by simpa using hk1)]
    have hcmp : decide (lowVal pBytes (k.val + 1) ≤ lowVal x (k.val + 1)) =
        (if xi = pi then res else decide (pi < xi)) := by
      rw [lowVal_succ, lowVal_succ, hres]
      have := cmp_step (lowVal x k.val) (lowVal pBytes k.val) (x.val[k.val]!).val
        (pBytes.val[k.val]!).val (256 ^ k.val) (lowVal_lt x k.val) (lowVal_lt pBytes k.val)
      rw [← hxv, ← hpv] at this ⊢
      by_cases he : xi = pi
      · have hv : xi.val = pi.val := by rw [he]
        rw [if_pos he, decide_eq_decide]; rw [if_pos hv] at this; exact this
      · have hv : xi.val ≠ pi.val := fun h => he (UScalar.eq_of_val_eq h)
        rw [if_neg he, decide_eq_decide]; rw [if_neg hv] at this; exact this
    split
    · rename_i hne
      step as ⟨k1, hk1v⟩
      apply ih k1 (by omega)
      rw [hk1v, hcmp, if_neg (by simpa using hne)]
    · rename_i hne
      step as ⟨k1, hk1v⟩
      apply ih k1 (by omega)
      have he : xi = pi := UScalar.eq_of_val_eq (by simpa using hne)
      rw [hk1v, hcmp, if_pos he]

open Aeneas.Std.WP in
/-- The reference `geq_p x` is `p ≤ x`. -/
theorem geq_p_spec (x : Array U8 32#usize) :
    ristretto_ref.geq_p x ⦃ b => b = decide (2 ^ 255 - 19 ≤ U8x32_as_Nat x) ⦄ := by
  unfold ristretto_ref.geq_p
  have h := geq_p_loop_spec x 32 0#usize (by simp) true (by simp [lowVal])
  rw [pBytes_val] at h
  have hx : lowVal x 32 = U8x32_as_Nat x := (U8x32_as_Nat_eq x).symm
  rw [hx] at h
  exact h

/-- `geq_p` as an equation. -/
theorem geq_p_eq (x : Array U8 32#usize) :
    ristretto_ref.geq_p x = ok (decide (2 ^ 255 - 19 ≤ U8x32_as_Nat x)) := by
  obtain ⟨v, hv, hP⟩ := eq_ok_of_spec (geq_p_spec x)
  rw [hv, hP]

end RistrettoSim
