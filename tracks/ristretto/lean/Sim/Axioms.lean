import Sim.Encode

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

/--
info: 'RistrettoSim.compress_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RistrettoSim.compress_refines

/--
info: 'RistrettoSim.decompress_compress_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RistrettoSim.decompress_compress_refines

/--
info: 'RistrettoSim.p58_field' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms RistrettoSim.p58_field
