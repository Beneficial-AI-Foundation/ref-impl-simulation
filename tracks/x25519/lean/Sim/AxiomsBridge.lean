import Sim.EdwardsBridge

/-! Each check fails if the axioms of the theorem differ from the standard three. -/

/-- info: 'X25519Sim.EdwardsBridge.toU_dblY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsBridge.toU_dblY

/-- info: 'X25519Sim.EdwardsBridge.toU_dblY_curve25519' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsBridge.toU_dblY_curve25519

/-- info: 'X25519Sim.EdwardsBridge.dadd_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsBridge.dadd_core
