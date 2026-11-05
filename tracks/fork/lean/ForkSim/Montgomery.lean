import ForkSim.X25519
import Specs.Montgomery

/-! # curve25519-dalek 5.0.0 against the translated reference

The fork proves `MontgomeryPoint::mul_base_clamped` and `MontgomeryPoint::mul_clamped` equal
to its `curve25519.x25519` (`Specs/Montgomery.lean`). `ForkSim.X25519` proves the translated
reference equal to the same `x25519`. Composed, the dalek functions return the bytes of the
reference.

The fork's translation merges four builds: 64-bit and 32-bit, each with and without
`precomputed-tables`. A function with per-build bodies becomes a dispatch on `get_target`,
which returns an opaque `target`. The fork's specs hold for every value of `target`, so each
theorem here holds for the four builds. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.montgomery

namespace ForkSim

/-- A computation with a spec returns a value. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ p ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact absurd h (by rw [spec_vis]; exact id)
  | div => exact absurd h (by rw [spec_div]; exact id)

/-- Two byte arrays with the same value are equal. -/
theorem eq_of_asNat_8 {a b : Array U8 32#usize} (h : a.asNat 8 = b.asNat 8) : a = b :=
  Array.eq_of_asNat_eq h

/-- **`MontgomeryPoint::mul_base_clamped` refines the reference.** For every 32-byte `k`,
`mul_base_clamped k` returns the bytes of `x25519_secret_to_public k`. -/
theorem mul_base_clamped_refines (k : Array U8 32#usize) :
    MontgomeryPoint.mul_base_clamped k ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  apply spec_mono (MontgomeryPoint.mul_base_clamped_spec k)
  intro r hr
  obtain ⟨r', hr', hval⟩ := exists_ok_of_spec (x25519_secret_to_public_spec k)
  rw [hr', eq_of_asNat_8 (hval.trans (hr.symm.trans (MontgomeryPoint.asNat_def r)))]

/-- **`MontgomeryPoint::mul_clamped` refines the reference.** For all 32-byte `u` and `k`,
`mul_clamped u k` returns the bytes of `x25519_scalarmult k u`. -/
theorem mul_clamped_refines (u k : Array U8 32#usize) :
    MontgomeryPoint.mul_clamped u k ⦃ r =>
      x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  apply spec_mono (MontgomeryPoint.mul_clamped_spec u k)
  intro r hr
  obtain ⟨r', hr', hval⟩ := exists_ok_of_spec (x25519_scalarmult_spec k u)
  rw [MontgomeryPoint.asNat_def] at hr
  rw [hr', eq_of_asNat_8 (hval.trans hr.symm)]

end ForkSim
