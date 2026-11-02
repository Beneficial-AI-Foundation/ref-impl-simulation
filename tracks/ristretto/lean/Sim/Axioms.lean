import Sim.Decode

/-! Axiom checks. The build fails if a list changes. -/

/--
info: 'RistrettoSim.decompress_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RistrettoSim.decompress_refines

/--
info: 'RistrettoSim.sqrt_ratio_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RistrettoSim.sqrt_ratio_i_refines
