import X25519Ref.Funs
import Curve25519Dalek.Math.Basic

/-! # Bytes and natural numbers

`U8x32_as_Nat` reads 32 bytes in little-endian order. The reference field model reads and
writes bytes with its own formulas (`fe_from_bytes`, `fe_to_bytes`). This file shows that the
two readings agree, and that clearing bit 255 is `% 2 ^ 255`. -/

open Aeneas Aeneas.Std Result

namespace X25519Sim

theorem digits_lt (f : ℕ → ℕ) (hf : ∀ j, f j < 256) :
    ∀ N, ∑ j ∈ Finset.range N, 256 ^ j * f j < 256 ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := hf N
    nlinarith [pow_pos (show 0 < 256 by norm_num) N]

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

theorem byte_lt (b : Array U8 32#usize) (j : ℕ) : (b.val[j]!).val < 256 := by
  have := (b.val[j]!).hBounds
  simpa using this

/-- Byte `i` of `b` is digit `i` of `U8x32_as_Nat b`. -/
theorem U8x32_digit (b : Array U8 32#usize) (i : ℕ) (hi : i < 32) :
    U8x32_as_Nat b / 256 ^ i % 256 = (b.val[i]!).val := by
  rw [U8x32_as_Nat_eq]
  exact digits_get (fun j => (b.val[j]!).val) (byte_lt b) 32 i hi

/-- If `b` reads as `a.val`, then `fe_to_bytes a` returns `b`. -/
theorem fe_to_bytes_eq (a : _root_.field.Fe) (b : Array U8 32#usize)
    (h : U8x32_as_Nat b = (show ZMod _root_.field.p from a).val) :
    _root_.field.fe_to_bytes a = ok b := by
  unfold _root_.field.fe_to_bytes
  simp only [ok.injEq]
  apply Aeneas.Std.Array.ext
  rw [Array.from_val]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    apply UScalar.eq_of_val_eq
    rw [UScalar.ofNatCore_val_eq, ← h, U8x32_digit b i (by simpa using h1),
      getElem!_pos b.val i h2]

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

/-- `fe_from_bytes` reads the bytes as `U8x32_as_Nat`, reduced mod p. -/
theorem fe_from_bytes_eq (b : Array U8 32#usize) :
    _root_.field.fe_from_bytes b =
      ok (show _root_.field.Fe from ((U8x32_as_Nat b : ℕ) : ZMod _root_.field.p)) := by
  unfold _root_.field.fe_from_bytes
  rw [foldr_horner (fun i => (b.val[i]!).val) 0 32, U8x32_as_Nat_eq, mul_zero, add_zero]

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

end X25519Sim
