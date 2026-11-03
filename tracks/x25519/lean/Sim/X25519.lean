import Sim.Full
import X25519Dalek.Funs

/-! # Full refinement: the X25519 functions of x25519-dalek

`x25519_refines`: `x25519_dalek::x25519` against `x25519_scalarmult`. The three
`*_diffie_hellman_refines`: `diffie_hellman` of `StaticSecret`, `EphemeralSecret` and
`ReusableSecret` against `x25519_scalarmult`. `x25519_basepoint_refines`: `x25519` on
`X25519_BASEPOINT_BYTES` against `x25519_secret_to_public`. The accessors `to_bytes` and
`as_bytes` are the identity. Each refinement theorem composes `mul_clamped_refines` with one
wrapper step.

Aeneas translates `StaticSecret`, `EphemeralSecret`, `ReusableSecret`, `PublicKey` and
`SharedSecret` to `Array U8 32#usize`. libsignal computes
`self.secret.diffie_hellman(&PublicKey::from(u)).as_bytes()`. In the theorems, `s` is the
bytes that `self.secret` wraps and `u` is the argument of `PublicKey::from`. The
`From<[u8; 32]>` impls are not extracted. Their bodies are tuple constructors, so they are the
identity on these bytes. This step rests on review of the Rust source (README section 4).
`EphemeralSecret::diffie_hellman` takes `self` by value. The extraction has no call to the
`Drop` impl of `EphemeralSecret`, so its Lean body is that of `StaticSecret`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace X25519Sim

open DalekSim

/-- `x25519 k u` returns the bytes of `x25519_scalarmult k u`. -/
theorem x25519_refines (k u : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k u ⦃ r =>
      x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  unfold x25519_dalek.x25519.x25519
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u k)
  rw [hr, bind_ok]
  simp only [curve25519_dalek.montgomery.MontgomeryPoint.to_bytes, spec_ok]
  exact hspec

/-- `StaticSecret.diffie_hellman s u` returns the bytes of `x25519_scalarmult s u`. -/
theorem static_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.StaticSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.StaticSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-- `StaticSecret.diffie_hellman s u` followed by `SharedSecret.as_bytes` returns the bytes
of `x25519_scalarmult s u`. -/
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

/-- `EphemeralSecret.diffie_hellman s u` returns the bytes of `x25519_scalarmult s u`. -/
theorem ephemeral_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.EphemeralSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.EphemeralSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-- `ReusableSecret.diffie_hellman s u` returns the bytes of `x25519_scalarmult s u`. -/
theorem reusable_diffie_hellman_refines (s u : Array U8 32#usize) :
    x25519_dalek.x25519.ReusableSecret.diffie_hellman s u ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  unfold x25519_dalek.x25519.ReusableSecret.diffie_hellman
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u s)
  rw [hr, bind_ok]
  exact (spec_ok r).mpr hspec

/-! ## Accessors

Each accessor returns its argument. -/

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

/-- `x25519 k X25519_BASEPOINT_BYTES` returns the bytes of `x25519_secret_to_public k`, the
public key of RFC 7748, section 6.1. -/
theorem x25519_basepoint_refines (k : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k x25519_dalek.x25519.X25519_BASEPOINT_BYTES ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  unfold x25519_ref.x25519_secret_to_public
  simp only [basepoint_eq, bind_ok]
  exact x25519_refines k _

end X25519Sim
