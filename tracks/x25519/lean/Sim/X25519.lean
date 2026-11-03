import Sim.Full
import X25519Dalek.Funs

/-! # Full refinement: x25519-dalek against the reference `x25519_scalarmult`

`x25519_dalek::x25519(k, u)` is `MontgomeryPoint(u).mul_clamped(k).to_bytes()`. The theorem
`x25519_refines` composes `mul_clamped_refines` with the extracted `to_bytes`, which returns
the bytes of the point.

`StaticSecret::diffie_hellman(&self, their_public)` is
`SharedSecret(their_public.0.mul_clamped(self.0))`. libsignal's
`PrivateKey::calculate_agreement(&self, u)` computes
`self.secret.diffie_hellman(&PublicKey::from(u)).as_bytes()`, where `self.secret` is a stored
`StaticSecret`. Aeneas translates `StaticSecret`, `PublicKey` and `SharedSecret` to
`Array U8 32#usize`. In the theorems below, `s` is the bytes that `self.secret` wraps and
`u` is the argument of `PublicKey::from`. The `From<[u8; 32]>` impls are not extracted.
Their bodies are the tuple constructors, so they are the identity on these bytes. This
step rests on review of the Rust source (README section 4). -/

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

/-- For all 32-byte `s` and `u`, `StaticSecret.diffie_hellman s u` returns `ok r` for some
`r`, with no panic, overflow or divergence, and `x25519_scalarmult s u = ok r`. -/
theorem static_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.StaticSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.StaticSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-- For all 32-byte `s` and `u`, `StaticSecret.diffie_hellman s u` followed by
`SharedSecret.as_bytes` returns `ok r` for some `r`, with no panic, overflow or divergence,
and `x25519_scalarmult s u = ok r`. -/
theorem static_diffie_hellman_as_bytes_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.StaticSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.as_bytes ss) ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (static_diffie_hellman_refines s u)
  rw [hr, bind_ok]
  simp only [x25519_dalek.x25519.SharedSecret.as_bytes,
    curve25519_dalek.montgomery.MontgomeryPoint.as_bytes, spec_ok]
  exact hspec

end X25519Sim
