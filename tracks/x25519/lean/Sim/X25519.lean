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

/-- For all 32-byte `s` and `u`, `EphemeralSecret.diffie_hellman s u` returns `ok r` for some
`r`, with no panic, overflow or divergence, and `x25519_scalarmult s u = ok r`. The Rust
method takes `self` by value, and the secret is erased when it is dropped. Aeneas does not
translate the drop, so the Lean body is the body of `StaticSecret.diffie_hellman`. -/
theorem ephemeral_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.EphemeralSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.EphemeralSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-- For all 32-byte `s` and `u`, `ReusableSecret.diffie_hellman s u` returns `ok r` for some
`r`, with no panic, overflow or divergence, and `x25519_scalarmult s u = ok r`. -/
theorem reusable_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.ReusableSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.ReusableSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-! ## Accessors

Aeneas translates `PublicKey`, `StaticSecret` and `SharedSecret` to `Array U8 32#usize`. Each
accessor returns its argument, so it preserves the relation of the theorems above. -/

/-- `SharedSecret::to_bytes` returns the bytes of the shared secret. -/
theorem shared_secret_to_bytes_eq (ss : Array U8 32#usize) :
    x25519_dalek.x25519.SharedSecret.to_bytes ss = ok ss := rfl

/-- `SharedSecret::as_bytes` returns the bytes of the shared secret. -/
theorem shared_secret_as_bytes_eq (ss : Array U8 32#usize) :
    x25519_dalek.x25519.SharedSecret.as_bytes ss = ok ss := rfl

/-- `PublicKey::to_bytes` returns the bytes of the public key. -/
theorem public_key_to_bytes_eq (pk : Array U8 32#usize) :
    x25519_dalek.x25519.PublicKey.to_bytes pk = ok pk := rfl

/-- `PublicKey::as_bytes` returns the bytes of the public key. -/
theorem public_key_as_bytes_eq (pk : Array U8 32#usize) :
    x25519_dalek.x25519.PublicKey.as_bytes pk = ok pk := rfl

/-- `StaticSecret::to_bytes` returns the bytes of the secret. -/
theorem static_secret_to_bytes_eq (s : Array U8 32#usize) :
    x25519_dalek.x25519.StaticSecret.to_bytes s = ok s := rfl

/-- `StaticSecret::as_bytes` returns the bytes of the secret. -/
theorem static_secret_as_bytes_eq (s : Array U8 32#usize) :
    x25519_dalek.x25519.StaticSecret.as_bytes s = ok s := rfl

/-! ## The base point -/

/-- `X25519_BASEPOINT_BYTES` is the base point of the reference: 32 zero bytes with byte 0
set to 9, as `x25519_secret_to_public` builds it. -/
theorem basepoint_eq :
    Array.update (Array.repeat 32#usize 0#u8) 0#usize 9#u8 =
      ok x25519_dalek.x25519.X25519_BASEPOINT_BYTES := by
  unfold x25519_dalek.x25519.X25519_BASEPOINT_BYTES
  rfl

/-- For every 32-byte scalar `k`, `x25519 k X25519_BASEPOINT_BYTES` returns without panic,
overflow or divergence, and the reference `x25519_secret_to_public k` returns the same bytes.
This is the public key of RFC 7748, section 6.1, through the bare function. -/
theorem x25519_basepoint_refines (k : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k x25519_dalek.x25519.X25519_BASEPOINT_BYTES ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  unfold x25519_ref.x25519_secret_to_public
  simp only [basepoint_eq, bind_ok]
  exact x25519_refines k _

end X25519Sim
