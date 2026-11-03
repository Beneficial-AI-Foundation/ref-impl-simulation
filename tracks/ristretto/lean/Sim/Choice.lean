import Sim.Field
import Sim.Bytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # `subtle` operations and the byte tests of dalek

The hand definitions of `subtle` (`Curve25519Dalek/FunsExternal.lean`) on the values 0 and 1,
the slice `ct_eq` on two 32-byte arrays, and the field tests `ct_eq`, `is_negative`, `is_zero`
and `conditional_assign`, stated over `toZ`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace RistrettoSim

instance : NeZero (2 ^ 255 - 19) := ⟨by norm_num⟩

/-- The `Choice` with value 1. -/
def cOne : subtle.Choice := ⟨1#u8, Or.inr rfl⟩
/-- The `Choice` with value 0. -/
def cZero : subtle.Choice := ⟨0#u8, Or.inl rfl⟩

theorem choice_eq (c : subtle.Choice) : c = cOne ∨ c = cZero := by
  rcases c with ⟨v, hv⟩
  rcases hv with h | h
  · right; subst h; rfl
  · left; subst h; rfl

theorem u8_and_one (x : U8) (hx : x = 0#u8 ∨ x = 1#u8) : x &&& 1#u8 = x := by
  rcases hx with h | h <;> subst h <;> decide

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

/-- `to_bytes` returns the canonical digits of the field element. -/
theorem to_bytes_val (f : FE) :
    backend.serial.u64.field.FieldElement51.to_bytes f
      ⦃ r => U8x32_as_Nat r = (toZ f).val ⦄ := by
  apply spec_mono (backend.serial.u64.field.FieldElement51.to_bytes_spec f)
  rintro r ⟨h1, h2⟩
  simp only [toZ]
  rw [← Nat.mod_eq_of_lt h2]
  exact h1

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

/-- The field `ct_eq` returns 1 iff the two elements are equal in `ZMod p`. -/
theorem ct_eq_z (a b : FE) :
    backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq.ct_eq a b
      ⦃ c => (c.val = 1#u8 ↔ toZ a = toZ b) ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq.ct_eq
  simp only [lift, bind_ok]
  step with to_bytes_val as ⟨ra, ha⟩
  step with to_bytes_val as ⟨rb, hb⟩
  apply spec_mono (slice_ct_eq_arr ra rb)
  intro c hc
  rw [hc]
  constructor
  · rintro rfl; exact ZMod.val_injective _ (ha.symm.trans hb)
  · intro h; apply U8x32_inj; rw [ha, hb, h]

/-- `Choice::from` on a value that is 0 or 1. -/
theorem choice_from_01 (x : U8) (hx : x = 0#u8 ∨ x = 1#u8) :
    subtle.Choice.Insts.CoreConvertFromU8.from x ⦃ c => c.val = x ⦄ := by
  unfold subtle.Choice.Insts.CoreConvertFromU8.from
  rcases hx with h | h
  · rw [dif_pos h, spec_ok]
  · rw [dif_neg (by rw [h]; decide), dif_pos h, spec_ok]

/-- The low bit of the first byte is the parity of the value. -/
theorem byte0_parity (r : Array U8 32#usize) : (r.val[0]!).val % 2 = U8x32_as_Nat r % 2 := by
  have hd := U8x32_digit r 0 (by norm_num)
  simp only [pow_zero, Nat.div_one] at hd
  rw [← hd, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 256)]

/-- `is_negative` returns 1 iff the canonical representative is odd. -/
theorem is_negative_z (a : FE) :
    field.FieldElement51.is_negative a
      ⦃ c => (c.val = 1#u8 ↔ (toZ a).val % 2 = 1) ⦄ := by
  unfold field.FieldElement51.is_negative
  simp only [lift, bind_ok]
  step with to_bytes_val as ⟨r, hr⟩
  step as ⟨i, hi⟩
  have hand : (i &&& 1#u8).val = (r.val[0]!).val % 2 := by
    rw [UScalar.val_and, hi, ← getElem!_pos r.val 0 (by simp)]
    exact Nat.and_one_is_mod _
  have h01 : i &&& 1#u8 = 0#u8 ∨ i &&& 1#u8 = 1#u8 := by
    rcases Nat.mod_two_eq_zero_or_one (r.val[0]!).val with h | h
    · left; apply UScalar.eq_of_val_eq; rw [hand, h]; rfl
    · right; apply UScalar.eq_of_val_eq; rw [hand, h]; rfl
  apply spec_mono (choice_from_01 _ h01)
  intro c hc
  rw [hc, ← hr, ← byte0_parity]
  constructor
  · intro h; rw [← hand, h]; rfl
  · intro h; apply UScalar.eq_of_val_eq; rw [hand, h]; rfl

theorem U8x32_zero : U8x32_as_Nat (Array.repeat 32#usize 0#u8) = 0 := by
  simp [U8x32_as_Nat, Array.getElem!_Nat_eq, Array.repeat_val]
  intro i hi
  interval_cases i <;> rfl

/-- `is_zero` returns 1 iff the element is 0 in `ZMod p`. -/
theorem is_zero_z (a : FE) :
    field.FieldElement51.is_zero a ⦃ c => (c.val = 1#u8 ↔ toZ a = 0) ⦄ := by
  unfold field.FieldElement51.is_zero
  simp only [lift, bind_ok]
  step with to_bytes_val as ⟨r, hr⟩
  apply spec_mono (slice_ct_eq_arr r _)
  intro c hc
  rw [hc]
  constructor
  · rintro rfl
    rw [U8x32_zero] at hr
    exact (ZMod.val_eq_zero _).mp hr.symm
  · intro h
    apply U8x32_inj
    rw [hr, U8x32_zero, h]
    exact ZMod.val_zero (n := 2 ^ 255 - 19)

/-- `conditional_assign` on field elements returns `b` iff the choice is 1. -/
theorem conditional_assign_eq (a b : FE) (c : subtle.Choice) :
    backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign
      a b c ⦃ r => r = if c.val = 1#u8 then b else a ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign
  unfold U64.Insts.SubtleConditionallySelectable.conditional_assign
  by_cases hc : c.val = 1#u8
  · simp only [hc, if_true, bind_ok]
    step*
    apply (Aeneas.Std.Array.eq_iff _ _).mpr
    have hb : b.val.length = 5 := by simp
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have : i < 5 := by simpa using h2
    interval_cases i <;> simp_all
  · simp only [hc, if_false, bind_ok]
    step*
    apply (Aeneas.Std.Array.eq_iff _ _).mpr
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have : i < 5 := by simpa using h2
    interval_cases i <;> simp_all

end RistrettoSim
