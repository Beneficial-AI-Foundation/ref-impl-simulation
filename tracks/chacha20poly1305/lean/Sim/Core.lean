import Aeneas
import Ref.Funs
import Real.Funs
import Sim.Basic
import Sim.Rounds
import Sim.CoreSplit
import Sim.CoreTail
open Aeneas Aeneas.Std Result WP

namespace Sim

/-- Loop invariant of the hacspec `add_state` loop: words before `start` are unchanged,
words from `start` on get `a[j] + b[j]`. -/
theorem add_state_loop_spec (n : Nat) : ∀ (r : core.ops.range.Range Std.Usize)
    (a b : Std.Array Std.U32 16#usize), r.end = 16#usize → r.start.val + n = 16 →
    Ref.hacspec_helper.add_state_loop r a b ⦃ out => ∀ j < 16,
      out.val[j]! = if j < r.start.val then a.val[j]!
        else core.num.U32.wrapping_add a.val[j]! b.val[j]! ⦄ := by
  induction n with
  | zero =>
    intro r a b he hs
    rw [Ref.hacspec_helper.add_state_loop]
    step
    have hlt : ¬ r.start.val < r.end.val := by rw [he]; simp at hs ⊢; omega
    simp only [hlt, ↓reduceIte] at o_post
    rw [o_post.1]
    simp only [spec_ok]
    intro j hj
    simp [show j < r.start.val by omega]
  | succ n ih =>
    intro r a b he hs
    rw [Ref.hacspec_helper.add_state_loop]
    step
    have hlt : r.start.val < r.end.val := by rw [he]; simp at hs ⊢; omega
    simp only [hlt, ↓reduceIte] at o_post
    obtain ⟨ho, hs1⟩ := o_post
    subst ho
    simp only
    have hi : r.start.val < 16 := by rw [he] at hlt; simpa using hlt
    step*
    rw [out_post j j_post]
    simp only [hs1, a_post, Array.set_val_eq]
    by_cases hjs : j < r.start.val
    · simp [show j < r.start.val + 1 by omega, hjs, Nat.ne_of_lt hjs]
    · by_cases hje : j = r.start.val
      · subst hje; simp [i1_post, i2_post, i3_post, hi]
      · simp [show ¬ j < r.start.val + 1 by omega, hjs, Ne.symm hje]

theorem list_ext16 {l1 l2 : List Std.U32} (n : Nat) (h1 : l1.length = n) (h2 : l2.length = n)
    (h : ∀ j < n, l1[j]! = l2[j]!) : l1 = l2 := by
  apply List.ext_getElem (by omega)
  intro j hj1 hj2
  have := h j (by omega)
  rwa [getElem!_pos l1 j hj1, getElem!_pos l2 j hj2] at this

set_option maxRecDepth 8192 in
theorem core_refines (k ctx : Slice Std.U32) (st0 : Std.Array Std.U32 16#usize) (ctr : Std.U32)
    (hk : k.length = 16) (hc : ctx.val = st0.val) :
    Real.hacl.chacha20.chacha20_core k ctx ctr
      ⦃ r => ∃ s, Ref.chacha20_core ctr st0 = .ok s ∧ r.val = s.val ⦄ := by
  have hcl : ctx.length = 16 := by simp [Slice.length, hc]
  obtain ⟨x, hx, hxv⟩ := spec_eq_ok (Array.index_usize_spec st0 12#usize (by simp))
  obtain ⟨st01, hst01, hst01v⟩ := spec_eq_ok
    (Array.update_spec st0 12#usize (core.num.U32.wrapping_add x ctr) (by simp))
  have href : Ref.chacha20_core ctr st0 =
      (do let k ← Ref.chacha20_rounds st01; Ref.hacspec_helper.add_state st01 k) := by
    rw [Ref.chacha20_core, hx]
    simp only [lift, Std.bind_ok, hst01]
  rw [href, Real.core_split]
  step*
  have hk2 : k2.val = st01.val := by
    apply list_ext16 16 (by rw [k2_post, s_post2]; simp [hk]) (by simp)
    intro j hj
    simp only [k2_post, i1_post, i_post, s2_post, s_post2, hst01v, hxv, Slice.set_val_eq,
      Array.set_val_eq]
    have hkl : k.val.length = 16 := hk
    have hcl' : ctx.val.length = 16 := hcl
    have hks : (k.setSlice! 0 s1.val).val = st0.val := by
      apply list_ext16 16 (by simp [hk]) (by simp)
      intro m hm
      have hs1l : s1.val.length = 16 := by simp [s1_post, hcl']
      have := Slice.setSlice!_getElem!_middle k s1.val 0 m (by simp [hs1l, hk]; omega)
      rw [Slice.getElem!_Nat_eq] at this
      rw [this, s1_post, ← hc]
      simp [hcl', hm]
    simp only [hks]
    by_cases hj12 : j = 12
    · subst hj12; simp
    · simp [Ne.symm hj12]
  refine lockstep_bind_tc (fun (r : Slice Std.U32) (s : Std.Array Std.U32 16#usize) => r.val = s.val) ?_ ?_
  · exact rounds_refines k2 _ hk2
  intro k3 kr hrel
  obtain ⟨out, hout, houtv⟩ := spec_eq_ok
    (add_state_loop_spec 16 { start := 0#usize, «end» := 16#usize } st01 kr rfl (by simp))
  rw [Ref.hacspec_helper.add_state, hout]
  simp only [ok.injEq, exists_eq_left']
  have hk3 : k3.length = 16 := by simp [Slice.length, hrel]
  apply WP.spec_mono (coreTail_spec k3 ctx ctr hk3 hcl)
  rintro r ⟨hrl, hrv⟩
  apply list_ext16 16 hrl (by simp)
  intro j hj
  rw [hrv j hj, houtv j hj]
  simp only [show ¬ (j < (0#usize : Usize).val) by simp, if_false]
  unfold tailWord
  rw [hrel, hc, hst01v, Array.set_val_eq]
  have hl0 : 12 < st0.val.length := by simp
  by_cases hj12 : j = 12
  · subst hj12
    have hx12 : x = st0.val[12]! := by rw [hxv, getElem!_pos st0.val 12 hl0]; rfl
    rw [show ((12#usize : Usize).val) = 12 by rfl, getElem!_set_self' _ _ _ hl0, if_pos rfl, hx12]
    exact wadd_word12 _ _ _
  · have hne : ((12#usize : Usize).val) ≠ j := by
      rw [show ((12#usize : Usize).val) = 12 by rfl]; exact Ne.symm hj12
    rw [getElem!_set_ne' _ _ _ _ hne, if_neg hj12, wadd_comm]


/-- `core_refines` at its call site in `chacha20_encrypt_block`, where the output buffer is
the fresh 16-word array `k`. Only the premise on `ctx` remains. -/
theorem core_refines_encrypt_block (ctx : Slice Std.U32) (st0 : Std.Array Std.U32 16#usize)
    (ctr : Std.U32) (hc : ctx.val = st0.val) :
    Real.hacl.chacha20.chacha20_core (Array.to_slice_mut (Array.repeat 16#usize 0#u32)).1 ctx ctr
      ⦃ r => ∃ s, Ref.chacha20_core ctr st0 = .ok s ∧ r.val = s.val ⦄ :=
  core_refines _ ctx st0 ctr (by simp [Array.to_slice_mut, Array.to_slice, Array.repeat, Slice.length]) hc

end Sim
