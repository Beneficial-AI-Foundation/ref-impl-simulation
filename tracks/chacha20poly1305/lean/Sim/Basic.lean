import Aeneas
open Aeneas Aeneas.Std Result Aeneas.Std.WP Aeneas.Data.Coinductive

namespace Sim

unseal Result in
/-- A total-correctness triple on `m` gives the concrete `ok` result. -/
theorem spec_eq_ok {α} {m : Result α} {p : α → Prop} (h : spec m p) : ∃ v, m = ok v ∧ p v := by
  unfold spec at h
  exact DWP.induction (θ := effectWP) (Q := fun value _ => p value)
    (P := fun (t : ITree RustEffect α) _ => ∃ v, t = ok v ∧ p v)
    (fun v _ hp => ⟨v, rfl, hp⟩) (fun e k s hwp => by cases e; exact hwp.elim) h

/-- Lockstep rule: one bind on each side, linked by a relation `R` on the intermediate results. -/
theorem lockstep_bind {α α' β β' : Type} {m : Result α} {m' : Result α'}
    {k : α → Result β} {k' : α' → Result β'}
    (R : α → α' → Prop) {Q : β → β' → Prop}
    (h1 : m ⦃ x => ∃ x', m' = ok x' ∧ R x x' ⦄)
    (h2 : ∀ x x', R x x' → k x ⦃ y => ∃ y', k' x' = ok y' ∧ Q y y' ⦄) :
    (Std.bind m k) ⦃ y => ∃ y', Std.bind m' k' = ok y' ∧ Q y y' ⦄ := by
  apply WP.spec_bind h1
  rintro x ⟨x', hm', hR⟩
  rw [hm', Std.bind_ok]
  exact h2 x x' hR

/-- `lockstep_bind` stated with the `do` (type class) bind that Aeneas emits. -/
theorem lockstep_bind_tc {α α' β β' : Type} {m : Result α} {m' : Result α'}
    {k : α → Result β} {k' : α' → Result β'}
    (R : α → α' → Prop) {Q : β → β' → Prop}
    (h1 : m ⦃ x => ∃ x', m' = ok x' ∧ R x x' ⦄)
    (h2 : ∀ x x', R x x' → k x ⦃ y => ∃ y', k' x' = ok y' ∧ Q y y' ⦄) :
    (do let x ← m; k x) ⦃ y => ∃ y', (do let x' ← m'; k' x') = ok y' ∧ Q y y' ⦄ :=
  lockstep_bind R h1 h2

/-- `next` on an `i32` range with `start < end`. The Aeneas library has this only for unsigned types. -/
theorem next_I32_some (r : core.ops.range.Range Std.I32) (h : r.start.val < r.end.val) :
    ∃ r', core.iter.range.IteratorRange.next core.iter.range.StepI32 r = ok (some r.start, r') ∧
      r'.start.val = r.start.val + 1 ∧ r'.end = r.end := by
  have hfwd : r.start.val + (1#usize).val ≤ IScalar.max .I32 := by scalar_tac
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32, core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked, core.cmp.PartialOrdI32, core.clone.CloneI32,
    liftFun1, liftFun2, core.cmp.impls.PartialOrdI32.lt, core.clone.impls.CloneI32.clone, h,
    decide_true, bind_tc_ok, ↓reduceIte, hfwd, ↓reduceDIte]
  refine ⟨_, rfl, ?_, rfl⟩
  simp only [IScalar.ofInt_val_eq]; rfl

/-- `next` on an exhausted `i32` range. -/
theorem next_I32_none (r : core.ops.range.Range Std.I32) (h : ¬ r.start.val < r.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 r = ok (none, r) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32, core.iter.range.IScalarStep,
    core.cmp.PartialOrdI32, liftFun2, core.cmp.impls.PartialOrdI32.lt, h,
    decide_false, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

end Sim
