import Sim.Pilot

/-! Each check fails if the axioms of the theorem differ from the standard three. -/

/-- info: 'X25519Sim.differential_add_and_double_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.differential_add_and_double_refines

/-- info: 'X25519Sim.point_add_and_double_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.point_add_and_double_eq
