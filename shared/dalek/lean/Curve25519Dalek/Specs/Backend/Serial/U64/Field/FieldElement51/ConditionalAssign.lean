/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Mathlib.Tactic

/-! # `FieldElement51::conditional_assign`

Sets each limb of `self` to the limb of `other` if `choice = 1` and leaves it unchanged
otherwise.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs#L250-L256"

Port note (ref-impl-simulation, Aeneas d119a474): the proof steps through the `u64` spec
`U64.Insts.SubtleConditionallySelectable.conditional_assign_spec` of `Specs/Subtle.lean`, in place
of unfolding the `u64` function and splitting on `choice`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- Each limb is `other`'s if `choice = 1`, else `self`'s. -/
@[step]
theorem conditional_assign_spec (self other : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (res : FieldElement51) =>
      (∀ i < 5, res[i]! = (if choice.val = 1#u8 then other[i]! else self[i]!)) ⦄ := by
  unfold conditional_assign
  step*
  intro i hi
  subst_vars
  interval_cases i <;> simp [*]

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
