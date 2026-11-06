import X25519Ref.Funs
import ForkSim.LadderMath

/-! # The reference X25519 in closed form

The `x25519_ref` functions that the ladder uses, as pure values: `scalar_bit` is `kbit`,
`point_add_and_double` is `LadderMath.pad`, `ladder_step` is `LadderMath.lstep`, and
`montgomery_ladder` is `LadderMath.ladder` over the 256 key bits from bit 255. Each of these
functions returns `ok`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open ForkSim.LadderMath

namespace ForkSim

/-- Bit `j` of a 32-byte little-endian scalar. -/
def kbit (k : Array U8 32#usize) (j : Nat) : Bool := (k.val[j / 8]!.val >>> (j % 8)) % 2 == 1

/-- The key bits from bit `n - 1` down to bit 0. -/
def bitsFrom (k : Array U8 32#usize) (n : Nat) : List Bool := (List.range n).reverse.map (kbit k)

/-- `bitsFrom k (n + 1) = kbit k n :: bitsFrom k n`. -/
theorem bitsFrom_succ (k : Array U8 32#usize) (n : Nat) :
    bitsFrom k (n + 1) = kbit k n :: bitsFrom k n := by
  simp [bitsFrom, List.range_succ]

/-- For `i < 256`, `scalar_bit k i` returns `kbit k i`. -/
@[step]
theorem scalar_bit_spec (k : Array U8 32#usize) (i : Usize) (hi : i.val < 256) :
    x25519_ref.scalar_bit k i ⦃ b => b = kbit k i.val ⦄ := by
  unfold x25519_ref.scalar_bit
  step*
  have h8 : i.val / 8 < k.val.length := by simp; omega
  have hi5 : i5.val = (k.val[i.val / 8]!.val >>> (i.val % 8)) % 2 := by
    simp [i5_post, i4_post, i2_post, i3_post, i1_post, getElem!_pos k.val (i.val / 8) h8,
      Nat.and_one_is_mod]
  have e : (i5 = 1#u8) ↔ i5.val = 1 :=
    ⟨fun h => by simp [h], fun h => UScalar.eq_of_val_eq (by simp [h])⟩
  simp only [kbit, ← hi5, e]
  cases h : (i5.val == 1) <;> simp_all

/-- `fe_lit x` is the value of `x` in the field. -/
@[simp] theorem fe_lit_eq (x : U32) : _root_.field.fe_lit x = ok ((x.val : ℕ) : _root_.field.Fe) :=
  rfl

/-- The reference ladder step in closed form. It is total. -/
theorem point_add_and_double_eq (x1 z1 x2 z2 x3 z3 : _root_.field.Fe) :
    x25519_ref.point_add_and_double (x1, z1) ((x2, z2), (x3, z3)) =
      ok (((x2 + z2) ^ 2 * ((x2 - z2) * (x2 - z2)),
           ((x2 + z2) ^ 2 - (x2 - z2) * (x2 - z2)) *
             ((x2 + z2) ^ 2 + 121665 * ((x2 + z2) ^ 2 - (x2 - z2) * (x2 - z2)))),
          (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) ^ 2,
           x1 * ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) ^ 2)) := by
  simp only [x25519_ref.point_add_and_double, _root_.field.fe_add, _root_.field.fe_sub,
    _root_.field.fe_mul, _root_.field.fe_sq, fe_lit_eq, bind_ok]
  rfl

/-- `point_add_and_double` is `pad`. -/
theorem point_add_and_double_pad (q : _root_.field.Fe × _root_.field.Fe)
    (S : (_root_.field.Fe × _root_.field.Fe) × (_root_.field.Fe × _root_.field.Fe)) :
    x25519_ref.point_add_and_double q S = ok (pad q.1 S) := by
  obtain ⟨x1, z1⟩ := q
  obtain ⟨⟨x2, z2⟩, ⟨x3, z3⟩⟩ := S
  rw [point_add_and_double_eq]
  rfl

/-- For `i < 256`, `ladder_step k init acc i` returns `lstep init.1 (kbit k (255 - i)) acc`. -/
theorem ladder_step_eq (k : Array U8 32#usize) (init : _root_.field.Fe × _root_.field.Fe)
    (acc : (_root_.field.Fe × _root_.field.Fe) × (_root_.field.Fe × _root_.field.Fe))
    (i : Usize) (hi : i.val < 256) :
    x25519_ref.ladder_step k init acc i ⦃ r => r = lstep init.1 (kbit k (255 - i.val)) acc ⦄ := by
  obtain ⟨P, Q⟩ := acc
  unfold x25519_ref.ladder_step
  step*
  all_goals
    have hb : 255 - i.val = i1.val := by omega
    rw [hb]; subst b_post
    simp_all [x25519_ref.swap, point_add_and_double_pad, lstep, cswap, pad]

/-- For `i + n = 256`, `ladder_loop k init acc i` terminates and returns
`ladder init.1 (bitsFrom k n) acc`: the iterations on bits `n - 1, …, 0`. -/
theorem ladder_loop_eq (k : Array U8 32#usize) (init : _root_.field.Fe × _root_.field.Fe) :
    ∀ (n : Nat) (i : Usize)
      (acc : (_root_.field.Fe × _root_.field.Fe) × (_root_.field.Fe × _root_.field.Fe)),
      i.val + n = 256 →
      x25519_ref.ladder_loop k init acc i ⦃ r => r = ladder init.1 (bitsFrom k n) acc ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i acc h
    rw [x25519_ref.ladder_loop]
    have : ¬ (i < 256#usize) := by scalar_tac
    simp [this, bitsFrom]
  | succ n ih =>
    intro i acc h
    rw [x25519_ref.ladder_loop]
    have hlt : i < 256#usize := by scalar_tac
    simp only [hlt, ite_true]
    step with ladder_step_eq as ⟨r, hr⟩
    step as ⟨i1, hi1⟩
    apply spec_mono (ih i1 r (by omega))
    intro r' hr'
    rw [hr', hr, bitsFrom_succ, ladder_cons, show 255 - i.val = n by omega]

/-- The reference bits: bit 255 down to bit 0. -/
abbrev refBits (k : Array U8 32#usize) : List Bool := bitsFrom k 256

/-- `montgomery_ladder k init` returns the first point of
`ladder init.1 (refBits k) ((1, 0), init)`: 256 iterations from bit 255. -/
theorem montgomery_ladder_eq (k : Array U8 32#usize) (init : _root_.field.Fe × _root_.field.Fe) :
    x25519_ref.montgomery_ladder k init ⦃ r => r = (ladder init.1 (refBits k) ((1, 0), init)).1 ⦄ := by
  unfold x25519_ref.montgomery_ladder
  simp only [fe_lit_eq, UScalar.ofNatCore_val_eq, Nat.cast_one, Nat.cast_zero, bind_ok]
  apply spec_bind (ladder_loop_eq k init 256 0#usize _ (by simp))
  intro r hr
  rw [hr]
  obtain ⟨P, Q⟩ := ladder init.1 (refBits k) ((1, 0), init)
  exact (spec_ok P).mpr rfl

/-- `encode_point` is `fe_to_bytes` of `enc`. -/
theorem encode_point_eq (P : _root_.field.Fe × _root_.field.Fe) :
    x25519_ref.encode_point P = _root_.field.fe_to_bytes (P.1 * P.2⁻¹) := by
  obtain ⟨x, z⟩ := P
  simp [x25519_ref.encode_point, _root_.field.fe_inv, _root_.field.fe_mul]

end ForkSim
