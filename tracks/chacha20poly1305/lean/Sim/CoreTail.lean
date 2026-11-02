import Aeneas
import Real.Funs
import Sim.CoreSplit
import Sim.Basic
open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Sim

/-- The `unroll_for!` loop counters of HACL `chacha20_core` are constants. -/
@[step] theorem core_i0 : Real.hacl.chacha20.chacha20_core.i ⦃ x => x = 0#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i; step*
@[step] theorem core_i1 : Real.hacl.chacha20.chacha20_core.i_1 ⦃ x => x = 1#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_1; step*
@[step] theorem core_i2 : Real.hacl.chacha20.chacha20_core.i_2 ⦃ x => x = 2#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_2; step*
@[step] theorem core_i3 : Real.hacl.chacha20.chacha20_core.i_3 ⦃ x => x = 3#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_3; step*
@[step] theorem core_i4 : Real.hacl.chacha20.chacha20_core.i_4 ⦃ x => x = 4#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_4; step*
@[step] theorem core_i5 : Real.hacl.chacha20.chacha20_core.i_5 ⦃ x => x = 5#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_5; step*
@[step] theorem core_i6 : Real.hacl.chacha20.chacha20_core.i_6 ⦃ x => x = 6#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_6; step*
@[step] theorem core_i7 : Real.hacl.chacha20.chacha20_core.i_7 ⦃ x => x = 7#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_7; step*
@[step] theorem core_i8 : Real.hacl.chacha20.chacha20_core.i_8 ⦃ x => x = 8#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_8; step*
@[step] theorem core_i9 : Real.hacl.chacha20.chacha20_core.i_9 ⦃ x => x = 9#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_9; step*
@[step] theorem core_i10 : Real.hacl.chacha20.chacha20_core.i_10 ⦃ x => x = 10#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_10; step*
@[step] theorem core_i11 : Real.hacl.chacha20.chacha20_core.i_11 ⦃ x => x = 11#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_11; step*
@[step] theorem core_i12 : Real.hacl.chacha20.chacha20_core.i_12 ⦃ x => x = 12#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_12; step*
@[step] theorem core_i13 : Real.hacl.chacha20.chacha20_core.i_13 ⦃ x => x = 13#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_13; step*
@[step] theorem core_i14 : Real.hacl.chacha20.chacha20_core.i_14 ⦃ x => x = 14#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_14; step*
@[step] theorem core_i15 : Real.hacl.chacha20.chacha20_core.i_15 ⦃ x => x = 15#u32 ⦄ := by
  unfold Real.hacl.chacha20.chacha20_core.i_15; step*

/-! The HACL tail after the rounds, one block per word, in the form `coreTail` has after the
index constants are evaluated. -/

theorem core_i0_eq : Real.hacl.chacha20.chacha20_core.i = ok 0#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i0; rw [hv, h]
theorem core_i1_eq : Real.hacl.chacha20.chacha20_core.i_1 = ok 1#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i1; rw [hv, h]
theorem core_i2_eq : Real.hacl.chacha20.chacha20_core.i_2 = ok 2#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i2; rw [hv, h]
theorem core_i3_eq : Real.hacl.chacha20.chacha20_core.i_3 = ok 3#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i3; rw [hv, h]
theorem core_i4_eq : Real.hacl.chacha20.chacha20_core.i_4 = ok 4#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i4; rw [hv, h]
theorem core_i5_eq : Real.hacl.chacha20.chacha20_core.i_5 = ok 5#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i5; rw [hv, h]
theorem core_i6_eq : Real.hacl.chacha20.chacha20_core.i_6 = ok 6#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i6; rw [hv, h]
theorem core_i7_eq : Real.hacl.chacha20.chacha20_core.i_7 = ok 7#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i7; rw [hv, h]
theorem core_i8_eq : Real.hacl.chacha20.chacha20_core.i_8 = ok 8#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i8; rw [hv, h]
theorem core_i9_eq : Real.hacl.chacha20.chacha20_core.i_9 = ok 9#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i9; rw [hv, h]
theorem core_i10_eq : Real.hacl.chacha20.chacha20_core.i_10 = ok 10#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i10; rw [hv, h]
theorem core_i11_eq : Real.hacl.chacha20.chacha20_core.i_11 = ok 11#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i11; rw [hv, h]
theorem core_i12_eq : Real.hacl.chacha20.chacha20_core.i_12 = ok 12#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i12; rw [hv, h]
theorem core_i13_eq : Real.hacl.chacha20.chacha20_core.i_13 = ok 13#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i13; rw [hv, h]
theorem core_i14_eq : Real.hacl.chacha20.chacha20_core.i_14 = ok 14#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i14; rw [hv, h]
theorem core_i15_eq : Real.hacl.chacha20.chacha20_core.i_15 = ok 15#u32 := by
  obtain ⟨v, hv, h⟩ := spec_eq_ok core_i15; rw [hv, h]

theorem wadd_comm (a b : Std.U32) :
    core.num.U32.wrapping_add a b = core.num.U32.wrapping_add b a := by
  rw [UScalar.eq_equiv_bv_eq]; simp only [core.num.U32.wrapping_add_bv_eq]; ac_rfl

/-- The word-12 identity: HACL adds `ctr` after `ctx[12]`, the reference before the rounds. -/
theorem wadd_word12 (a b c : Std.U32) :
    core.num.U32.wrapping_add (core.num.U32.wrapping_add a b) c =
      core.num.U32.wrapping_add (core.num.U32.wrapping_add b c) a := by
  rw [UScalar.eq_equiv_bv_eq]; simp only [core.num.U32.wrapping_add_bv_eq]; ac_rfl

/-- The back function of `split_at_mut s 0`, in a form that `simp` can apply. -/
def back0 {T : Type} (s : Slice T) (p : Slice T × Slice T) : Slice T :=
  if p.1.length = 0 ∧ p.2.length = s.length then p.2 else s

theorem split_at_mut_zero_eq {T : Type} (s : Slice T) :
    core.slice.Slice.split_at_mut s 0#usize =
      ok ((Slice.from [] (by simp), s), back0 s) := by
  unfold core.slice.Slice.split_at_mut
  simp only [UScalar.ofNatCore_val_eq, zero_le, ↓reduceDIte]
  congr 1
  ext1
  · ext1
    · apply Slice.ext; simp [List.splitAt_eq]
    · apply Slice.ext; simp [List.splitAt_eq]
  · funext p
    dsimp only [back0]
    by_cases h : p.1.length = 0 ∧ p.2.length = s.length
    · have h0 : p.1.val = [] := by simpa [Slice.length] using h.1
      rw [dif_pos (by simp [Slice.length, List.splitAt_eq] at *; exact h), if_pos h]
      apply Slice.ext; simp [h0]
    · rw [dif_neg (by simp [Slice.length, List.splitAt_eq] at *; exact h), if_neg h]

@[simp] theorem back0_apply {T : Type} (s t : Slice T) (h) (ht : t.length = s.length) :
    back0 s (Slice.from [] h, t) = t := by
  simp [back0, ht]

/-- Expected value of word `j` after the HACL tail. -/
def tailWord (k ctx : List Std.U32) (ctr : Std.U32) (j : Nat) : Std.U32 :=
  if j = 12 then core.num.U32.wrapping_add (core.num.U32.wrapping_add k[j]! ctx[j]!) ctr
  else core.num.U32.wrapping_add k[j]! ctx[j]!

/-- One unrolled block of the HACL tail, `k[i] = k[i] + ctx[i]`, after the split at 0 is
rewritten by `split_at_mut_zero_eq`. -/
def blk (k ctx : Slice Std.U32) (i : Std.U32) : Result (Slice Std.U32) := do
  let i3 ← lift (UScalar.cast .Usize i)
  let i4 ← Slice.index_usize k i3
  let i5 ← lift (UScalar.cast .Usize i)
  let i6 ← Slice.index_usize ctx i5
  let x ← lift (core.num.U32.wrapping_add i4 i6)
  let i7 ← lift (UScalar.cast .Usize i)
  let s5 ← Slice.update k i7 x
  ok (back0 k (Slice.from [] (by simp), s5))

set_option maxRecDepth 8192 in
theorem coreTail_eq (k0 ctx : Slice Std.U32) (ctr : Std.U32) :
    Real.coreTail k0 ctx ctr = (do
  let k1 ← blk k0 ctx 0#u32
  let k2 ← blk k1 ctx 1#u32
  let k3 ← blk k2 ctx 2#u32
  let k4 ← blk k3 ctx 3#u32
  let k5 ← blk k4 ctx 4#u32
  let k6 ← blk k5 ctx 5#u32
  let k7 ← blk k6 ctx 6#u32
  let k8 ← blk k7 ctx 7#u32
  let k9 ← blk k8 ctx 8#u32
  let k10 ← blk k9 ctx 9#u32
  let k11 ← blk k10 ctx 10#u32
  let k12 ← blk k11 ctx 11#u32
  let k13 ← blk k12 ctx 12#u32
  let k14 ← blk k13 ctx 13#u32
  let k15 ← blk k14 ctx 14#u32
  let k16 ← blk k15 ctx 15#u32
  let i98 ← Slice.index_usize k16 12#usize
  let i99 ← lift (core.num.U32.wrapping_add i98 ctr)
  Slice.update k16 12#usize i99) := by
  unfold Real.coreTail blk
  simp only [core_i0_eq, core_i1_eq, core_i2_eq, core_i3_eq, core_i4_eq, core_i5_eq, core_i6_eq, core_i7_eq, core_i8_eq, core_i9_eq, core_i10_eq, core_i11_eq, core_i12_eq, core_i13_eq, core_i14_eq, core_i15_eq, split_at_mut_zero_eq, Std.bind_ok, uncurry_apply_pair, Std.bind_assoc]

theorem getElem!_set_self' {α : Type} [Inhabited α] (l : List α) (i : Nat) (a : α)
    (h : i < l.length) : (l.set i a)[i]! = a := by
  rw [getElem!_pos (l.set i a) i (by simp [h])]; simp

theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) (i j : Nat) (a : α)
    (hij : i ≠ j) : (l.set i a)[j]! = l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, hij]

/-- After `n` blocks, words below `n` hold `k0[j] + ctx[j]` and the others are unchanged. -/
def TailInv (k0 ctx : List Std.U32) (n : Nat) (k : Slice Std.U32) : Prop :=
  k.length = 16 ∧ ∀ j < 16, k.val[j]! =
    if j < n then core.num.U32.wrapping_add k0[j]! ctx[j]! else k0[j]!

theorem blk_spec (k0 : List Std.U32) (ctx : Slice Std.U32) (n : Nat) (i : Std.U32)
    (hi : i.val = n) (hn : n < 16) (k : Slice Std.U32) (hc : ctx.length = 16)
    (h : TailInv k0 ctx.val n k) :
    blk k ctx i ⦃ k' => TailInv k0 ctx.val (n + 1) k' ⦄ := by
  obtain ⟨hl, hv⟩ := h
  unfold blk
  step*
  have hcast : ∀ u : Usize, u = UScalar.cast .Usize i → u.val = n := by
    intro u hu; subst hu; simp [hi]
  have h3 := hcast i3 i3_post
  have h5 := hcast i5 i5_post
  have h7 := hcast i7 i7_post
  rw [back0_apply _ _ _ (by rw [s5_post]; simp)]
  refine ⟨by rw [s5_post]; simp [hl], fun j hj => ?_⟩
  rw [s5_post, Slice.set_val_eq, h7]
  by_cases hjn : j = n
  · subst hjn
    have hk := hv j hj
    simp only [lt_irrefl, if_false] at hk
    have hlk : j < k.val.length := by simp [Slice.length] at hl; omega
    have hlc : j < ctx.val.length := by simp [Slice.length] at hc; omega
    simp only [getElem!_set_self' _ _ _ hlk, Nat.lt_succ_self, if_true, x_post, i4_post, i6_post, h3, h5]
    rw [← getElem!_pos k.val j hlk, hk, ← getElem!_pos ctx.val j hlc]
  · rw [getElem!_set_ne' _ _ _ _ (Ne.symm hjn), hv j hj]
    have : (j < n + 1) = (j < n) := by apply propext; omega
    simp only [this]

set_option maxRecDepth 8192 in
theorem coreTail_spec (k0 ctx : Slice Std.U32) (ctr : Std.U32)
    (hk : k0.length = 16) (hc : ctx.length = 16) :
    Real.coreTail k0 ctx ctr ⦃ r => r.length = 16 ∧ ∀ j < 16, r.val[j]! = tailWord k0.val ctx.val ctr j ⦄ := by
  rw [coreTail_eq]
  have h0 : TailInv k0.val ctx.val 0 k0 := ⟨hk, fun j _ => by simp⟩
  refine WP.spec_bind (blk_spec k0.val ctx 0 0#u32 (by simp) (by omega) k0 hc h0) ?_
  intro k1 h1
  refine WP.spec_bind (blk_spec k0.val ctx 1 1#u32 (by simp) (by omega) k1 hc h1) ?_
  intro k2 h2
  refine WP.spec_bind (blk_spec k0.val ctx 2 2#u32 (by simp) (by omega) k2 hc h2) ?_
  intro k3 h3
  refine WP.spec_bind (blk_spec k0.val ctx 3 3#u32 (by simp) (by omega) k3 hc h3) ?_
  intro k4 h4
  refine WP.spec_bind (blk_spec k0.val ctx 4 4#u32 (by simp) (by omega) k4 hc h4) ?_
  intro k5 h5
  refine WP.spec_bind (blk_spec k0.val ctx 5 5#u32 (by simp) (by omega) k5 hc h5) ?_
  intro k6 h6
  refine WP.spec_bind (blk_spec k0.val ctx 6 6#u32 (by simp) (by omega) k6 hc h6) ?_
  intro k7 h7
  refine WP.spec_bind (blk_spec k0.val ctx 7 7#u32 (by simp) (by omega) k7 hc h7) ?_
  intro k8 h8
  refine WP.spec_bind (blk_spec k0.val ctx 8 8#u32 (by simp) (by omega) k8 hc h8) ?_
  intro k9 h9
  refine WP.spec_bind (blk_spec k0.val ctx 9 9#u32 (by simp) (by omega) k9 hc h9) ?_
  intro k10 h10
  refine WP.spec_bind (blk_spec k0.val ctx 10 10#u32 (by simp) (by omega) k10 hc h10) ?_
  intro k11 h11
  refine WP.spec_bind (blk_spec k0.val ctx 11 11#u32 (by simp) (by omega) k11 hc h11) ?_
  intro k12 h12
  refine WP.spec_bind (blk_spec k0.val ctx 12 12#u32 (by simp) (by omega) k12 hc h12) ?_
  intro k13 h13
  refine WP.spec_bind (blk_spec k0.val ctx 13 13#u32 (by simp) (by omega) k13 hc h13) ?_
  intro k14 h14
  refine WP.spec_bind (blk_spec k0.val ctx 14 14#u32 (by simp) (by omega) k14 hc h14) ?_
  intro k15 h15
  refine WP.spec_bind (blk_spec k0.val ctx 15 15#u32 (by simp) (by omega) k15 hc h15) ?_
  intro k16 h16
  obtain ⟨hl16, hv16⟩ := h16
  step*
  refine ⟨by rw [r_post]; simp [hl16], fun j hj => ?_⟩
  have hl : 12 < k16.val.length := by simp [Slice.length] at hl16; omega
  have h12 := hv16 12 (by omega)
  simp only [show (12 : Nat) < 15 + 1 by omega, if_true] at h12
  rw [r_post, Slice.set_val_eq]
  unfold tailWord
  by_cases hj12 : j = 12
  · subst hj12
    simp only [show ((12#usize : Usize).val) = 12 by rfl, getElem!_set_self' _ _ _ hl, if_true,
      i99_post, i98_post]
    rw [← getElem!_pos k16.val 12 hl, h12]
  · have hne : ((12#usize : Usize).val) ≠ j := by
      rw [show ((12#usize : Usize).val) = 12 by rfl]; exact Ne.symm hj12
    rw [getElem!_set_ne' _ _ _ _ hne, hv16 j hj, if_neg hj12, if_pos (by omega)]

end Sim
