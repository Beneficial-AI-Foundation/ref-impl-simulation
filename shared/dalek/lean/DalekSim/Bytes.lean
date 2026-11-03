import Curve25519Dalek.Math.Basic

/-! # Bytes and natural numbers

Lemmas about `U8x32_as_Nat`, which reads 32 bytes in little-endian order: its base-256
digits are the bytes, and clearing bit 255 is `% 2 ^ 255`. They do not depend on a
reference program. Tracks B and D use them to relate dalek's bytes to the byte functions of
their references. -/

open Aeneas Aeneas.Std Result

namespace DalekSim

/-- A number with `N` base-256 digits is below `256 ^ N`. -/
theorem digits_lt (f : ℕ → ℕ) (hf : ∀ j, f j < 256) :
    ∀ N, ∑ j ∈ Finset.range N, 256 ^ j * f j < 256 ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := hf N
    nlinarith [pow_pos (show 0 < 256 by norm_num) N]

/-- For `i < N`, digit `i` of `∑ j < N, 256 ^ j * f j` is `f i`, when every `f j < 256`. -/
theorem digits_get (f : ℕ → ℕ) (hf : ∀ j, f j < 256) :
    ∀ N, ∀ i < N, (∑ j ∈ Finset.range N, 256 ^ j * f j) / 256 ^ i % 256 = f i := by
  intro N
  induction N with
  | zero => intro i hi; omega
  | succ N ih =>
    intro i hi
    rw [Finset.sum_range_succ]
    have hpos : 0 < 256 ^ i := pow_pos (by norm_num) i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hsplit : 256 ^ N * f N = 256 ^ i * (256 * (256 ^ (N - i - 1) * f N)) := by
        rw [show (256 : ℕ) ^ N = 256 ^ i * 256 * 256 ^ (N - i - 1) by
          rw [← pow_succ, ← pow_add]; congr 1; omega]
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left, ih i hi]
    · rw [mul_comm, Nat.add_mul_div_right _ _ hpos,
        Nat.div_eq_of_lt (digits_lt f hf i), zero_add, Nat.mod_eq_of_lt (hf i)]

/-- `U8x32_as_Nat` as a sum of digits in base 256. -/
theorem U8x32_as_Nat_eq (b : Array U8 32#usize) :
    U8x32_as_Nat b = ∑ j ∈ Finset.range 32, 256 ^ j * (b.val[j]!).val := by
  unfold U8x32_as_Nat
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_mul, Array.getElem!_Nat_eq]; norm_num

/-- Every byte is below 256. -/
theorem byte_lt (b : Array U8 32#usize) (j : ℕ) : (b.val[j]!).val < 256 := by
  have := (b.val[j]!).hBounds
  simpa using this

/-- Byte `i` of `b` is digit `i` of `U8x32_as_Nat b`. -/
theorem U8x32_digit (b : Array U8 32#usize) (i : ℕ) (hi : i < 32) :
    U8x32_as_Nat b / 256 ^ i % 256 = (b.val[i]!).val := by
  rw [U8x32_as_Nat_eq]
  exact digits_get (fun j => (b.val[j]!).val) (byte_lt b) 32 i hi

/-- Horner's rule: `foldr (fun i acc => acc * 256 + g i) c (range n) =
∑ j < n, 256 ^ j * g j + 256 ^ n * c`. -/
theorem foldr_horner (g : ℕ → ℕ) (c : ℕ) : ∀ n,
    (List.range n).foldr (fun i acc => acc * 256 + g i) c =
      ∑ j ∈ Finset.range n, 256 ^ j * g j + 256 ^ n * c := by
  intro n
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih,
      Finset.sum_range_succ, pow_succ]
    ring

/-- Clearing the top bit of byte 31 is reduction mod `2 ^ 255`. -/
theorem U8x32_mask_top (u : Array U8 32#usize) (x : U8) (hx : x.val = (u.val[31]!).val % 128) :
    U8x32_as_Nat (u.set 31#usize x) = U8x32_as_Nat u % 2 ^ 255 := by
  rw [U8x32_as_Nat_eq, U8x32_as_Nat_eq, Finset.sum_range_succ _ 31, Finset.sum_range_succ _ 31]
  have hv : (u.set 31#usize x).val = u.val.set 31 x := by rw [Array.set_val_eq]; rfl
  have hlow : ∑ j ∈ Finset.range 31, 256 ^ j * ((u.set 31#usize x).val[j]!).val =
      ∑ j ∈ Finset.range 31, 256 ^ j * (u.val[j]!).val := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj : j < 31 := Finset.mem_range.mp hj
    have hl : j < u.val.length := by simp; omega
    rw [hv, getElem!_pos _ j (by simpa using hl), getElem!_pos _ j hl,
      List.getElem_set_ne (by omega)]
  have h31 : ((u.set 31#usize x).val[31]!).val = x.val := by
    rw [hv, getElem!_pos _ 31 (by simp), List.getElem_set_self]
  rw [hlow, h31, hx]
  have hA := digits_lt (fun j => (u.val[j]!).val) (byte_lt u) 31
  have hb := byte_lt u 31
  generalize ∑ j ∈ Finset.range 31, 256 ^ j * (u.val[j]!).val = A at hA ⊢
  generalize (u.val[31]!).val = c at hb ⊢
  norm_num at hA ⊢
  omega

end DalekSim
