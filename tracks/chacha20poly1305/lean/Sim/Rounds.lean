import Aeneas
import Ref.Funs
import Real.Funs
import Sim.Basic
import Sim.QuarterRound
open Aeneas Aeneas.Std Result WP

namespace Sim

/-- `k` hacspec double rounds in sequence. -/
def drN : Nat → Std.Array Std.U32 16#usize → Result (Std.Array Std.U32 16#usize)
  | 0, s => ok s
  | k + 1, s => do let s' ← Ref.chacha20_double_round s; drN k s'

/-- The hacspec rounds loop, started `k` steps before its end, runs `k` double rounds. -/
theorem ref_rounds_loop_eq (k : Nat) : ∀ (r : core.ops.range.Range Std.I32) s,
    r.end = 10#i32 → r.start.val + k = 10 → Ref.chacha20_rounds_loop r s = drN k s := by
  induction k with
  | zero =>
    intro r s he hs
    rw [Ref.chacha20_rounds_loop, next_I32_none r (by rw [he]; simp at hs ⊢; omega)]
    simp [drN]
  | succ k ih =>
    intro r s he hs
    obtain ⟨r', hn, hs', he'⟩ := next_I32_some r (by rw [he]; simp at hs ⊢; omega)
    have ih' := fun s' => ih r' s' (he'.trans he) (by omega)
    rw [Ref.chacha20_rounds_loop, hn]
    simp [ih', drN]

theorem ref_rounds_eq (s : Std.Array Std.U32 16#usize) : Ref.chacha20_rounds s = drN 10 s :=
  ref_rounds_loop_eq 10 _ s rfl (by simp)

/-- One lockstep bind over a double-round call on both sides. -/
macro "dr_bind" : tactic =>
  `(tactic| (
    refine lockstep_bind
      (fun (r : Slice Std.U32) (s : Std.Array Std.U32 16#usize) => r.val = s.val) ?_ ?_
    · apply double_round_refines; assumption
    intro _ _ _))

/-- The unrolled HACL rounds refine the hacspec rounds loop. -/
theorem rounds_refines (st : Slice Std.U32) (state : Std.Array Std.U32 16#usize)
    (hst : st.val = state.val) :
    Real.hacl.chacha20.rounds st
      ⦃ r => ∃ s, Ref.chacha20_rounds state = .ok s ∧ r.val = s.val ⦄ := by
  rw [ref_rounds_eq]
  simp only [drN, Std.bind_pure]
  unfold Real.hacl.chacha20.rounds
  dr_bind; dr_bind; dr_bind; dr_bind; dr_bind; dr_bind; dr_bind; dr_bind; dr_bind
  apply double_round_refines; assumption

end Sim
