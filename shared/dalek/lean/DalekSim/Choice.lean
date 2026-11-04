import Curve25519Dalek.Funs
import DalekSim.Bytes

/-! # The slice `ct_eq` of `subtle` on 32 bytes

Lemmas about the hand definitions of `subtle` (`Curve25519Dalek/FunsExternal.lean`) on the
values 0 and 1: the slice `ct_eq` on two 32-byte arrays returns 1 iff the arrays are equal.
Also the injectivity of `U8x32_as_Nat` and the value of 32 zero bytes. They do not depend on
a reference program. Tracks B and D use them for the byte tests of dalek. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace DalekSim

/-- `x & 1 = x` for `x` in `{0, 1}`. -/
theorem u8_and_one (x : U8) (hx : x = 0#u8 ∨ x = 1#u8) : x &&& 1#u8 = x := by
  rcases hx with h | h <;> subst h <;> decide

/-- `x & 0 = 0`. -/
theorem u8_and_zero (x : U8) : x &&& 0#u8 = 0#u8 := by
  apply UScalar.eq_of_val_eq
  simp

/-- The loop of the slice `ct_eq` over two lists of bytes of the same length. -/
theorem ct_eq_loop_u8 : ∀ (xs ys : List U8) (x : U8), xs.length = ys.length →
    (x = 0#u8 ∨ x = 1#u8) →
    ∃ y, Slice.Insts.SubtleConstantTimeEq.ct_eq_loop U8.Insts.SubtleConstantTimeEq xs ys x = ok y ∧
      (y = 0#u8 ∨ y = 1#u8) ∧ (y = 1#u8 ↔ x = 1#u8 ∧ xs = ys)
  | [], [], x, _, hx => ⟨x, rfl, hx, by simp⟩
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: xs, b :: ys, x, h, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    by_cases hab : a = b
    · have hc : x &&& (1#u8) = x := u8_and_one x hx
      obtain ⟨y, hy, hy01, hyiff⟩ := ct_eq_loop_u8 xs ys x h hx
      refine ⟨y, ?_, hy01, ?_⟩
      · simp only [Slice.Insts.SubtleConstantTimeEq.ct_eq_loop, U8.Insts.SubtleConstantTimeEq,
          U8.Insts.SubtleConstantTimeEq.ct_eq, hab, if_true, bind_ok]
        rw [hc]; exact hy
      · rw [hyiff, hab]; simp
    · obtain ⟨y, hy, hy01, hyiff⟩ := ct_eq_loop_u8 xs ys 0#u8 h (Or.inl rfl)
      refine ⟨y, ?_, hy01, ?_⟩
      · simp only [Slice.Insts.SubtleConstantTimeEq.ct_eq_loop, U8.Insts.SubtleConstantTimeEq,
          U8.Insts.SubtleConstantTimeEq.ct_eq, hab, if_false, bind_ok]
        rw [u8_and_zero]; exact hy
      · rw [hyiff]; simp [hab]

/-- The slice `ct_eq` on two 32-byte arrays returns 1 iff the arrays are equal. -/
theorem slice_ct_eq_arr (a b : Array U8 32#usize) :
    Slice.Insts.SubtleConstantTimeEq.ct_eq U8.Insts.SubtleConstantTimeEq
      (Array.to_slice a) (Array.to_slice b) ⦃ c => (c.val = 1#u8 ↔ a = b) ⦄ := by
  have hla : (Array.to_slice a).val.length = 32 := by simp [Array.to_slice]
  have hlb : (Array.to_slice b).val.length = 32 := by simp [Array.to_slice]
  obtain ⟨y, hy, hy01, hyiff⟩ := ct_eq_loop_u8 (Array.to_slice a).val (Array.to_slice b).val
    1#u8 (by rw [hla, hlb]) (Or.inr rfl)
  unfold Slice.Insts.SubtleConstantTimeEq.ct_eq
  have hlen : ¬ (Array.to_slice a).length ≠ (Array.to_slice b).length := by
    simp only [Slice.length, hla, hlb, ne_eq, not_not]
  rw [if_neg hlen, hy, bind_ok]
  unfold subtle.Choice.Insts.CoreConvertFromU8.from
  rcases hy01 with h0 | h1
  · rw [dif_pos h0, spec_ok]
    simp only [h0]
    constructor
    · intro h; exact absurd h (by decide)
    · intro hab; have := hyiff.mpr ⟨rfl, by rw [hab]⟩; rw [h0] at this; exact absurd this (by decide)
  · rw [dif_neg (by rw [h1]; decide), dif_pos h1, spec_ok]
    simp only [h1, true_iff]
    have := (hyiff.mp h1).2
    exact (Aeneas.Std.Array.eq_iff a b).mpr (by simpa [Array.to_slice] using this)

/-- Two byte arrays with the same value are equal. -/
theorem U8x32_inj (a b : Array U8 32#usize) (h : U8x32_as_Nat a = U8x32_as_Nat b) : a = b := by
  apply (Aeneas.Std.Array.eq_iff a b).mpr
  apply List.ext_getElem (by simp)
  intro i hia hib
  have ha32 : i < 32 := by simpa using hia
  have hd := U8x32_digit a i ha32
  rw [h, U8x32_digit b i ha32] at hd
  rw [← getElem!_pos a.val i hia, ← getElem!_pos b.val i hib]
  exact (UScalar.eq_of_val_eq hd).symm

/-- 32 zero bytes read as 0. -/
theorem U8x32_zero : U8x32_as_Nat (Array.repeat 32#usize 0#u8) = 0 := by
  simp [U8x32_as_Nat, Array.getElem!_Nat_eq, Array.repeat_val]
  intro i hi
  interval_cases i <;> rfl

end DalekSim
