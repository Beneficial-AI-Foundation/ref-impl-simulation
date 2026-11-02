import Sim.Discharge

/-! Each check fails if the axioms of the theorem differ from the standard three. -/

/-- info: 'X25519Sim.add_contract_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.add_contract_holds

/-- info: 'X25519Sim.sub_contract_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.sub_contract_holds

/-- info: 'X25519Sim.mul_contract_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.mul_contract_holds

/-- info: 'X25519Sim.square_contract_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.square_contract_holds

/-- info: 'X25519Sim.field_contracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.field_contracts

/-- info: 'X25519Sim.differential_add_and_double_refines_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X25519Sim.differential_add_and_double_refines_proved
