/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Support for the specs of `LookupTable`

`next_spec` gives the result of `next` on a range of `usize`: `none` and the same range if
the range is empty, otherwise its start and the range from the next index. The `Inhabited`
instances let `step` apply the Aeneas array specs to tables of `ProjectiveNielsPoint`.

Port note (ref-impl-simulation, Aeneas d119a474): curve25519-dalek-lean-verify proves
`next_spec` in `Specs/Scalar/Scalar/ConditionalSelect.lean`, in the namespace of the `Scalar`
instance, and defines the instances in `Specs/Window/LookupTable/From.lean`. The specs of
`from` and `select` use both. This file holds copies of these items only, under the same
names, so that the two specs share one copy and their proofs do not change.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

theorem next_spec (range : core.ops.range.Range Usize) :
    ∃ opt range',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range = ok (opt, range') ∧
      (¬ range.start.val < range.end.val → opt = none ∧ range' = range) ∧
      (range.start.val < range.end.val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.end = range.end) := by
  simp only [core.iter.range.IteratorRange.next,
    show core.iter.range.StepUsize.partialOrdInst.lt range.start range.end
      = ok (decide (range.start.val < range.end.val)) from rfl,
    show core.iter.range.StepUsize.cloneInst.clone range.start = ok range.start from rfl,
    bind_tc_ok]
  by_cases hlt : range.start.val < range.end.val
  · rw [if_pos (by simp [hlt])]
    simp only [core.iter.range.StepUsize, core.iter.range.UScalarStep,
      core.iter.range.UScalarStep.forward_checked,
      show range.start.val + (1#usize).val ≤ UScalar.max UScalarTy.Usize from by scalar_tac,
      ↓reduceDIte, bind_tc_ok]
    refine ⟨_, _, rfl, ?_, ?_⟩
    · intro h; exact absurd hlt h
    · intro _; refine ⟨rfl, ?_, rfl⟩; simp [UScalar.ofNatCore_val_eq]
  · rw [if_neg (by simp [hlt])]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

end curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

namespace curve25519_dalek.window

open backend.serial.curve_models

-- `step` applies the Aeneas array specs, which need `[Inhabited α]`.
instance : Inhabited ProjectiveNielsPoint where
  default := ⟨default, default, default, default⟩

end curve25519_dalek.window
