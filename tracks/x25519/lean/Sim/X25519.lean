import Sim.Full
import X25519Dalek.Funs

/-! # Full refinement: x25519-dalek's `x25519` against the reference `x25519_scalarmult`

`x25519_dalek::x25519(k, u)` is `MontgomeryPoint(u).mul_clamped(k).to_bytes()`. The theorem
`x25519_refines` composes `mul_clamped_refines` with the extracted `to_bytes`, which returns
the bytes of the point. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace X25519Sim

open DalekSim

/-- For every 32-byte scalar `k` and u-coordinate `u`, x25519-dalek's `x25519 k u` returns
without panic, overflow or divergence, and the reference `x25519_scalarmult k u` returns the
same bytes. -/
theorem x25519_refines (k u : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k u ⦃ r =>
      x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  unfold x25519_dalek.x25519.x25519
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u k)
  rw [hr, bind_ok]
  simp only [curve25519_dalek.montgomery.MontgomeryPoint.to_bytes, spec_ok]
  exact hspec

end X25519Sim
