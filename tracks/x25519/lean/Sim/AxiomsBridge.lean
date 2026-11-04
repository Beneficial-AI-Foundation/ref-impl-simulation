import Sim.EdwardsBridge
import Sim.EdwardsLadder
import Sim.BaseLadder

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

/-- info: 'X25519Sim.EdwardsLadder.dbl_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.dbl_rep

/-- info: 'X25519Sim.EdwardsLadder.dadd_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.dadd_rep

/-- info: 'X25519Sim.EdwardsLadder.ladder_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.ladder_rep

/-- info: 'X25519Sim.EdwardsLadder.enc_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.enc_ladder

/-- info: 'X25519Sim.EdwardsLadder.basePoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.basePoint

/-- info: 'X25519Sim.EdwardsLadder.enc_ladder_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.enc_ladder_nine

/-- info: 'X25519Sim.enc_ladder_nine_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.enc_ladder_nine_bytes

/-- info: 'X25519Sim.enc_ladder_nine_clamped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.enc_ladder_nine_clamped

/-- info: 'X25519Sim.dalekLadder_basepoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.dalekLadder_basepoint

/-- info: 'X25519Sim.mul_basepoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.mul_basepoint_spec

/-- info: 'X25519Sim.EdwardsLadder.basePoint_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.basePoint_y

/-- info: 'X25519Sim.EdwardsLadder.basePoint_x_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.basePoint_x_even

/-- info: 'X25519Sim.EdwardsLadder.toU_basePoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.EdwardsLadder.toU_basePoint
