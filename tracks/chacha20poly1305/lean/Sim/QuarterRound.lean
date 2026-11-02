import Aeneas
import Ref.Funs
import Real.Funs
import Sim.Basic
open Aeneas Aeneas.Std Result

namespace Sim

/-- One ChaCha20 line `a += b; d ^= a; d <<<= s` on a list of words (indices assumed distinct). -/
def lineModel (m : List Std.U32) (a b d : Nat) (s : Std.U32) : List Std.U32 :=
  let x := core.num.U32.wrapping_add m[a]! m[b]!
  (m.set a x).set d (core.num.U32.rotate_left (m[d]! ^^^ x) s)

/-- The reference line computes `lineModel` when `a ≠ d`. -/
@[step]
theorem ref_line_spec (a b d : Std.Usize) (s : Std.U32) (m : Std.Array Std.U32 16#usize)
    (ha : a.val < 16) (hb : b.val < 16) (hd : d.val < 16) (had : a.val ≠ d.val) :
    Ref.chacha20_line a b d s m ⦃ m' => m'.val = lineModel m.val a.val b.val d.val s ⦄ := by
  unfold Ref.chacha20_line
  step*
  have e5 : i5 = i3 ^^^ i4 := UScalar.eq_of_val_eq i5_post
  have hl : (m.val).length = 16 := by simp
  subst_vars
  simp [lineModel, List.set_set, Ne.symm had, hl, ha, hb, hd]

/-- HACL writes rotation as `(x << n) | (x >> (32 - n))`. -/
theorem rot (x : Std.U32) (n m : Std.U32) (hn : 0 < n.val ∧ n.val < 32) (hm : m.val = 32 - n.val) :
    (core.num.U32.wrapping_shl x n ||| core.num.U32.wrapping_shr x m)
      = core.num.U32.rotate_left x n := by
  rw [UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_or, core.num.U32.wrapping_shl_bv_eq, core.num.U32.wrapping_shr_bv_eq,
    core.num.U32.rotate_left, UScalar.rotate_left, BitVec.rotateLeft, BitVec.rotateLeftAux]
  have h1 : n.val % 32 = n.val := Nat.mod_eq_of_lt hn.2
  have h2 : (32 - n.val) % 32 = 32 - n.val := Nat.mod_eq_of_lt (by omega)
  simp only [hm, h1, h2, UScalarTy.numBits]
  rfl

theorem rot16 (x : Std.U32) : (core.num.U32.wrapping_shl x 16#u32 ||| core.num.U32.wrapping_shr x 16#u32)
    = core.num.U32.rotate_left x 16#u32 := rot x _ _ (by decide) (by decide)
theorem rot12 (x : Std.U32) : (core.num.U32.wrapping_shl x 12#u32 ||| core.num.U32.wrapping_shr x 20#u32)
    = core.num.U32.rotate_left x 12#u32 := rot x _ _ (by decide) (by decide)
theorem rot8 (x : Std.U32) : (core.num.U32.wrapping_shl x 8#u32 ||| core.num.U32.wrapping_shr x 24#u32)
    = core.num.U32.rotate_left x 8#u32 := rot x _ _ (by decide) (by decide)
theorem rot7 (x : Std.U32) : (core.num.U32.wrapping_shl x 7#u32 ||| core.num.U32.wrapping_shr x 25#u32)
    = core.num.U32.rotate_left x 7#u32 := rot x _ _ (by decide) (by decide)

@[step]
theorem slice_update_len_spec {α : Type} (v : Slice α) (i : Std.Usize) (x : α)
    (hbound : i.val < v.length) :
    v.update i x ⦃ nv => nv = v.set i x ∧ nv.length = v.length ⦄ := by
  have := Slice.update_spec v i x hbound
  apply WP.spec_mono this
  intro nv h; exact ⟨h, by simp [h]⟩

theorem cast_usize_val (x : Std.U32) (h : x.val < 16) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with h' | h' <;> simp [UScalarTy.numBits, h'] <;> omega

/-- Pilot: the HACL quarter round (slice, `u32` indices) refines the hacspec quarter round
(array, `usize` indices), with equal output words. -/
theorem quarter_round_refines
    (st : Slice Std.U32) (state : Std.Array Std.U32 16#usize)
    (a b c d : Std.U32) (a' b' c' d' : Std.Usize)
    (hst : st.val = state.val)
    (ha : a.val = a'.val) (hb : b.val = b'.val) (hc : c.val = c'.val) (hd : d.val = d'.val)
    (ha16 : a.val < 16) (hb16 : b.val < 16) (hc16 : c.val < 16) (hd16 : d.val < 16)
    (had : a.val ≠ d.val) (hcb : c.val ≠ b.val) :
    Real.hacl.chacha20.quarter_round st a b c d
      ⦃ r => ∃ s, Ref.chacha20_quarter_round a' b' c' d' state = .ok s ∧ r.val = s.val ⦄ := by
  have hlen : st.length = 16 := by simp [Slice.length, hst]
  unfold Real.hacl.chacha20.quarter_round
  step*
  apply spec_eq_ok
  unfold Ref.chacha20_quarter_round
  step*
  simp only [← UScalar.eq_equiv] at *
  have hl : st.val.length = 16 := hlen
  have h1 : st2.val = lineModel st.val a.val b.val d.val 16#u32 := by
    rw [st2_post, st1_post, std2_post, i3_post, i4_post, rot16, std1_post, sta1_post, sta_post,
      stb_post, std_post]
    simp only [Slice.set_val_eq, lineModel, i_post, i1_post, i2_post, i5_post, i6_post,
      cast_usize_val _ ha16, cast_usize_val _ hb16, cast_usize_val _ hd16]
    simp [hl, ha16, hb16, hd16]
  have hl2 : st2.val.length = 16 := by
    have : st2.length = 16 := by rw [st2_post1, st1_post1, hlen]
    exact this
  have h2 : st4.val = lineModel st2.val c.val d.val b.val 12#u32 := by
    rw [st4_post, st3_post, std20_post, i10_post, i11_post, rot12, std10_post, sta10_post,
      sta0_post, stb0_post, std0_post]
    simp only [Slice.set_val_eq, lineModel, i7_post, i8_post, i9_post, i12_post, i13_post,
      cast_usize_val _ hc16, cast_usize_val _ hb16, cast_usize_val _ hd16]
    simp [hl2, hc16, hb16, hd16]
  have hl4 : st4.val.length = 16 := by
    have : st4.length = 16 := by rw [st4_post1, st3_post1, st2_post1, st1_post1, hlen]
    exact this
  have h3 : st6.val = lineModel st4.val a.val b.val d.val 8#u32 := by
    rw [st6_post, st5_post, std21_post, i17_post, i18_post, rot8, std11_post, sta11_post,
      sta2_post, stb1_post, std3_post]
    simp only [Slice.set_val_eq, lineModel, i14_post, i15_post, i16_post, i19_post, i20_post,
      cast_usize_val _ ha16, cast_usize_val _ hb16, cast_usize_val _ hd16]
    simp [hl4, ha16, hb16, hd16]
  have hl6 : st6.val.length = 16 := by
    have : st6.length = 16 := by
      rw [st6_post1, st5_post1, st4_post1, st3_post1, st2_post1, st1_post1, hlen]
    exact this
  have h4 : r.val = lineModel st6.val c.val d.val b.val 7#u32 := by
    rw [r_post, st7_post, std22_post, i24_post, i25_post, rot7, std12_post, sta12_post,
      sta3_post, stb2_post, std4_post]
    simp only [Slice.set_val_eq, lineModel, i21_post, i22_post, i23_post, i26_post, i27_post,
      cast_usize_val _ hc16, cast_usize_val _ hb16, cast_usize_val _ hd16]
    simp [hl6, hc16, hb16, hd16]
  rw [h4, h3, h2, h1, v_post, state3_post, state2_post, state1_post, hst, ha, hb, hc, hd]

/-- Closes one quarter-round obligation with `quarter_round_refines` on literal indices. -/
macro "qr_close" : tactic =>
  `(tactic| (apply quarter_round_refines <;> first | assumption | decide))

/-- One lockstep bind over a quarter-round call on both sides. -/
macro "qr_bind" : tactic =>
  `(tactic| (
    refine lockstep_bind
      (fun (r : Slice Std.U32) (s : Std.Array Std.U32 16#usize) => r.val = s.val) ?_ ?_
    · qr_close
    intro _ _ _))

/-- The HACL double round refines the hacspec double round: eight lockstep quarter-round calls. -/
theorem double_round_refines (st : Slice Std.U32) (state : Std.Array Std.U32 16#usize)
    (hst : st.val = state.val) :
    Real.hacl.chacha20.double_round st
      ⦃ r => ∃ s, Ref.chacha20_double_round state = .ok s ∧ r.val = s.val ⦄ := by
  unfold Real.hacl.chacha20.double_round Ref.chacha20_double_round
  qr_bind; qr_bind; qr_bind; qr_bind; qr_bind; qr_bind; qr_bind
  qr_close

end Sim
