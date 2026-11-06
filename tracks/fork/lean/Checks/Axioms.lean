import ForkSim.Montgomery

/-! # Axiom checks

The reference theorems use only the three standard axioms. The dalek theorems add the
fork's models of three Rust crates, each one axiom that states that the crate's functions
meet their contracts:

- `RustAx.core`: `core` (`Curve25519Dalek/FunsExternal.lean` in the fork).
- `RustAx.subtle`: `subtle` (`Subtle/Contract.lean` in the fork).
- `RustAx.zeroize`: `zeroize` (`Zeroize/Contract.lean` in the fork). -/

/-- info: 'ForkSim.x25519_scalarmult_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.x25519_scalarmult_spec

/-- info: 'ForkSim.x25519_secret_to_public_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ForkSim.x25519_secret_to_public_spec

/--
info: 'ForkSim.mul_base_clamped_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle]
-/
#guard_msgs in #print axioms ForkSim.mul_base_clamped_refines

/--
info: 'ForkSim.mul_clamped_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RustAx.core,
 RustAx.subtle,
 RustAx.zeroize]
-/
#guard_msgs in #print axioms ForkSim.mul_clamped_refines
