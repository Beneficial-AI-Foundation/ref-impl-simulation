/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Alessandro D'Angelo,
  Hoang Le Truong, Markus Ferdinand Dablander
-/
import Curve25519Dalek.Funs

/-!
# Spec theorems for the `subtle` functions of `FunsExternal.lean`

The constants `Choice.zero` and `Choice.one`, their lemmas, and the specs of `ct_eq` on `u16`
and of `conditional_select` and `conditional_assign` on `u64`.

Port note (ref-impl-simulation, Aeneas d119a474): curve25519-dalek-lean-verify keeps these
items in its `FunsExternal.lean`, next to the definitions. Here `FunsExternal.lean` holds the
definitions only, so the items are copied to this file. The proofs are the same, except
`U16.Insts.SubtleConstantTimeEq.ct_eq_spec`, because the definition here writes the two
results as literals. `U64.Insts.SubtleConditionallySelectable.conditional_assign_spec` is new,
because the definition here does not call `conditional_select`. The spec of
`subtle.ConditionallySelectable.conditional_assign.default` is not copied, because no spec uses it.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace curve25519_dalek

/-- The `Choice` with value `0`. -/
def Choice.zero : subtle.Choice := { val := 0#u8, valid := Or.inl rfl }
/-- The `Choice` with value `1`. -/
def Choice.one : subtle.Choice := { val := 1#u8, valid := Or.inr rfl }

instance : DecidableEq subtle.Choice := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro heq; apply h; rw [heq])

/-- `c.val = 0 ∨ c.val = 1`. -/
theorem Choice.val_eq_zero_or_one (c : subtle.Choice) : c.val = 0#u8 ∨ c.val = 1#u8 := by
  cases c with
  | _ _ valid =>
    cases valid with
    | inl h => left; exact h
    | inr h => right; exact h

/-- `c = Choice.zero ∨ c = Choice.one`. -/
theorem Choice.eq_zero_or_one (c : subtle.Choice) : c = Choice.zero ∨ c = Choice.one := by
  cases c with
  | _ _ valid =>
    cases valid with
    | inl h => left; simpa [Choice.zero]
    | inr h => right; simpa [Choice.one]

@[simp] theorem Choice.one_ne_zero : Choice.one ≠ Choice.zero := by decide
@[simp] theorem Choice.zero_ne_one : Choice.zero ≠ Choice.one := by decide

@[simp] theorem Choice.ne_one_iff (c : subtle.Choice) : c ≠ Choice.one ↔ c = Choice.zero := by
  cases Choice.eq_zero_or_one c with
  | inl h => simp [h]
  | inr h => simp [h]

@[simp] theorem Choice.ne_zero_iff (c : subtle.Choice) : c ≠ Choice.zero ↔ c = Choice.one := by
  cases Choice.eq_zero_or_one c with
  | inl h => simp [h]
  | inr h => simp [h]

theorem Choice.eq_zero_of_val (c : subtle.Choice) (h : c.val = 0#u8) : c = Choice.zero := by
  cases c; simpa [Choice.zero]

theorem Choice.eq_one_of_val (c : subtle.Choice) (h : c.val = 1#u8) : c = Choice.one := by
  cases c; simpa [Choice.one]

/-- `c.val = 1 ↔ c = Choice.one`. -/
lemma Choice.val_eq_one_iff (c : subtle.Choice) :
    c.val = 1#u8 ↔ c = Choice.one := by
  cases c with
  | mk val valid =>
    simp [Choice.one]

/-- `ct_eq a b` returns `Choice.one` iff `a = b`. -/
@[step]
theorem U16.Insts.SubtleConstantTimeEq.ct_eq_spec
    (a b : U16) :
    U16.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ (c : subtle.Choice) =>
      (c = Choice.one ↔ a = b) ⦄ := by
  unfold U16.Insts.SubtleConstantTimeEq.ct_eq
  split
  · rename_i h_eq
    simp only [spec_ok]
    simp [h_eq, Choice.one]
  · rename_i h_ne
    simp only [spec_ok, h_ne, iff_false]
    intro h
    cases h

/-- `conditional_select a b choice` is `b` if `choice = 1`, else `a`. -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select
      a b choice ⦃ (res : U64) =>
      res = if choice.val = 1#u8 then b else a ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  split <;> simp_all

/-- `conditional_assign a b choice` returns `b` if `choice = 1`, else `a`. -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_assign
      a b choice ⦃ (res : U64) =>
      res = if choice.val = 1#u8 then b else a ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_assign
  split <;> simp_all

end curve25519_dalek
