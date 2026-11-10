import ForkSim.X25519Dalek

/-! # Axiom checks for x25519-dalek 3.0.0

The theorems of `ForkSim.X25519Dalek` add no axiom of their own. The translation of
x25519-dalek calls the fork's definitions (`X25519Dalek/FunsExternal.lean`), so the theorems use
the fork's models of three Rust crates:

- `RustAx.core`: `core` (`Curve25519Dalek/FunsExternal.lean` in the fork).
- `RustAx.subtle`: `subtle` (`Subtle/Contract.lean` in the fork).
- `RustAx.zeroize`: `zeroize` (`Zeroize/Contract.lean` in the fork). -/

/--
info: 'ForkSim.static_diffie_hellman_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.static_diffie_hellman_refines

/--
info: 'ForkSim.ephemeral_diffie_hellman_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.ephemeral_diffie_hellman_refines

/--
info: 'ForkSim.reusable_diffie_hellman_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.reusable_diffie_hellman_refines

/--
info: 'ForkSim.static_diffie_hellman_as_bytes_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.static_diffie_hellman_as_bytes_refines

/--
info: 'ForkSim.public_key_from_static_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkSim.public_key_from_static_refines

/--
info: 'ForkSim.public_key_from_ephemeral_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkSim.public_key_from_ephemeral_refines

/--
info: 'ForkSim.public_key_from_reusable_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkSim.public_key_from_reusable_refines

/--
info: 'ForkSim.x25519_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.x25519_refines

/--
info: 'ForkSim.x25519_basepoint_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.x25519_basepoint_refines

/-- info: 'ForkSim.basepoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.basepoint_eq

/-- info: 'ForkSim.static_secret_to_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.static_secret_to_bytes_eq

/-- info: 'ForkSim.static_secret_as_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.static_secret_as_bytes_eq

/-- info: 'ForkSim.public_key_to_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.public_key_to_bytes_eq

/-- info: 'ForkSim.public_key_as_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.public_key_as_bytes_eq

/-- info: 'ForkSim.shared_secret_to_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.shared_secret_to_bytes_eq

/-- info: 'ForkSim.shared_secret_as_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.shared_secret_as_bytes_eq

/-- info: 'ForkSim.static_secret_from_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.static_secret_from_eq

/-- info: 'ForkSim.public_key_from_bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.public_key_from_bytes_eq

/--
info: 'ForkSim.static_diffie_hellman_was_contributory_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.static_diffie_hellman_was_contributory_refines

/--
info: 'ForkSim.ephemeral_diffie_hellman_was_contributory_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.ephemeral_diffie_hellman_was_contributory_refines

/--
info: 'ForkSim.reusable_diffie_hellman_was_contributory_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.reusable_diffie_hellman_was_contributory_refines

/--
info: 'ForkSim.static_secret_drop_spec' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.static_secret_drop_spec

/--
info: 'ForkSim.reusable_secret_drop_spec' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.reusable_secret_drop_spec

/--
info: 'ForkSim.ephemeral_secret_drop_spec' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.ephemeral_secret_drop_spec

/--
info: 'ForkSim.shared_secret_drop_spec' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.shared_secret_drop_spec

/--
info: 'ForkSim.ephemeral_diffie_hellman_drop_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.ephemeral_diffie_hellman_drop_refines

/--
info: 'ForkSim.public_key_from_static_as_bytes_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkSim.public_key_from_static_as_bytes_refines

/-- info: 'ForkSim.public_key_clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.public_key_clone_eq

/-- info: 'ForkSim.static_secret_clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.static_secret_clone_eq

/-- info: 'ForkSim.reusable_secret_clone_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.reusable_secret_clone_eq

/-- info: 'ForkSim.public_key_as_ref_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.public_key_as_ref_eq

/-- info: 'ForkSim.static_secret_as_ref_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.static_secret_as_ref_eq

/-- info: 'ForkSim.shared_secret_as_ref_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.shared_secret_as_ref_eq

/-- info: 'ForkSim.public_key_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs in #print axioms ForkSim.public_key_eq_spec

/-- info: 'ForkSim.ephemeral_random_from_rng_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.ephemeral_random_from_rng_spec

/-- info: 'ForkSim.reusable_random_from_rng_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.reusable_random_from_rng_spec

/-- info: 'ForkSim.static_random_from_rng_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.static_random_from_rng_spec

/-- info: 'ForkSim.public_key_zeroize_spec' depends on axioms: [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs in #print axioms ForkSim.public_key_zeroize_spec
