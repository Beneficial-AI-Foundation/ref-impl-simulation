import Curve25519Dalek.Funs

/-! # Limb bounds and `Result` lemmas

Definitions and lemmas about the real code that do not depend on a reference program.
Tracks B and D use them. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace DalekSim

/-- Every limb of a `FieldElement51` is below `2 ^ k`. -/
def Bnd (k : Nat) (f : backend.serial.u64.field.FieldElement51) : Prop :=
  ∀ i < 5, (f[i]!).val < 2 ^ k

/-- A limb bound holds for every larger exponent. -/
theorem bnd_mono {j k : Nat} {f : backend.serial.u64.field.FieldElement51} (h : Bnd j f)
    (hjk : j ≤ k) : Bnd k f :=
  fun i hi => lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by norm_num) hjk)

/-- A total-correctness triple gives a returned value: `m ⦃ P ⦄ → ∃ v, m = ok v ∧ P v`. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ v, m = ok v ∧ P v := by
  cases m with
  | ret a => exact ⟨a, rfl, (spec_ok (p := P) a).mp h⟩
  | vis e k => exact ((spec_vis (p := P) e k).mp h).elim
  | div => exact ((spec_div (p := P)).mp h).elim

/-- `m ⦃ r => r = v ⦄ → m = ok v`. -/
theorem eq_ok_of_spec {α : Type} {m : Result α} {v : α} (h : m ⦃ r => r = v ⦄) : m = ok v := by
  obtain ⟨w, hw, rfl⟩ := exists_ok_of_spec h
  exact hw

end DalekSim
