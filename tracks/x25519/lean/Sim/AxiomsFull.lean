import Sim.Full
import Sim.X25519

/-! Each check fails if the axioms of the theorem differ from the standard three. -/

/-- info: 'X25519Sim.mul_clamped_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.mul_clamped_refines

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.to_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.to_bytes_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes_spec

/-- info: 'curve25519_dalek.field.FieldElement51.invert_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.field.FieldElement51.invert_spec

/-- info: 'X25519Sim.x25519_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.x25519_refines

/-- info: 'X25519Sim.static_diffie_hellman_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.static_diffie_hellman_refines

/-- info: 'X25519Sim.static_diffie_hellman_as_bytes_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.static_diffie_hellman_as_bytes_refines
