import Sim.Full
import X25519Dalek.Funs

/-! # Full refinement: x25519-dalek against the reference `x25519_scalarmult`

`x25519_dalek::x25519(k, u)` is `MontgomeryPoint(u).mul_clamped(k).to_bytes()`. The theorem
`x25519_refines` composes `mul_clamped_refines` with the extracted `to_bytes`, which returns
the bytes of the point.

`StaticSecret::diffie_hellman(&self, their_public)` is
`SharedSecret(their_public.0.mul_clamped(self.0))`. libsignal's `calculate_agreement` calls
it on `StaticSecret::from(s)` and `PublicKey::from(u)`, then reads the result with
`SharedSecret::as_bytes`. Aeneas translates the three newtypes `StaticSecret`, `PublicKey`
and `SharedSecret` to the 32-byte array, and each `From<[u8; 32]>` impl is the tuple
constructor. So the bytes `s` and `u` in the theorems below are `StaticSecret::from(s)` and
`PublicKey::from(u)`. Charon cannot start from a method of a generic trait impl, so the two
`from` functions are not in the extraction. -/

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

/-- For every 32-byte secret `s` and public key `u`, x25519-dalek's
`StaticSecret::diffie_hellman` returns without panic, overflow or divergence, and the
reference `x25519_scalarmult s u` returns the bytes of the shared secret. -/
theorem static_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.StaticSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.StaticSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-- The call of libsignal's `calculate_agreement`:
`StaticSecret::from(s).diffie_hellman(&PublicKey::from(u)).as_bytes()` returns the bytes of
the reference `x25519_scalarmult s u`. -/
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
