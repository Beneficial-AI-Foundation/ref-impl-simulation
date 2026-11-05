import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Identity
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Neg
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjective
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjectiveNiels
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Double
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByPow2
import Curve25519Dalek.Specs.Window.LookupTable.From
import Curve25519Dalek.Specs.Window.LookupTable.Select

/-!
# Axioms of the point specs

Each spec of this list states a result of `toPoint` in the group `DalekSim.Edwards.Point dEd`:
an equality of points, a sum, a scalar multiple, the identity or a negation. `#guard_msgs`
checks that each spec depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. So no spec depends on the `sorry` in the associativity of the group of
curve25519-dalek-lean-verify. The build fails if the axioms change.
-/

/--
info: 'curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_extended_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_extended_spec

/--
info: 'curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_projective_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_projective_spec

/--
info: 'curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add_spec

/--
info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_point

/--
info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/--
info: 'curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec

/--
info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec

/--
info: 'curve25519_dalek.backend.serial.curve_models.ProjectivePoint.double_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectivePoint.double_spec

/--
info: 'curve25519_dalek.edwards.EdwardsPoint.as_projective_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.edwards.EdwardsPoint.as_projective_spec

/--
info: 'curve25519_dalek.edwards.EdwardsPoint.as_projective_niels_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.edwards.EdwardsPoint.as_projective_niels_spec

/--
info: 'curve25519_dalek.edwards.EdwardsPoint.double_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.edwards.EdwardsPoint.double_spec

/--
info: 'curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/--
info: 'curve25519_dalek.edwards.EdwardsPoint.mul_by_pow_2_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.edwards.EdwardsPoint.mul_by_pow_2_spec

/--
info: 'curve25519_dalek.window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_spec

/--
info: 'curve25519_dalek.window.LookupTable.select_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms curve25519_dalek.window.LookupTable.select_spec
