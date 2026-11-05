/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Subtle

/-! # `FieldElement51::conditional_select`

Returns, limb by limb, `b` if `choice = 1` and `a` otherwise.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs#L228-L240"

Port note (ref-impl-simulation, Aeneas d119a474): the file imports `Specs/Subtle.lean`. The proof
steps through `U64.Insts.SubtleConditionallySelectable.conditional_select_spec`, in place of
unfolding the `u64` function and proving the two cases of `choice` separately.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- Each limb is `b`'s if `choice = 1`, else `a`'s. -/
@[step]
theorem conditional_select_spec
    (a b : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (res : FieldElement51) =>
      ∀ i < 5,
        res[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!) ⦄ := by
  unfold conditional_select
  step*
  intro i hi
  subst_vars
  simp only [Array.getElem!_Nat_eq, Array.make, List.getElem!_eq_getElem?_getD]
  rcases i with _ | _ | _ | _ | _ | n <;> simp_all
  omega

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
