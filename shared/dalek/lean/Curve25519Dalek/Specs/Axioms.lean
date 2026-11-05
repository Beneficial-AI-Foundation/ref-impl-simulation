import Curve25519Dalek.Specs.Backend.Serial.CurveModels.AffineNielsPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.AffineNielsPoint.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.AffineNielsPoint.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.AffineNielsPoint.Identity
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.AffineNielsPoint.Neg
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Identity
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Neg
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EdwardsD2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsAffineNiels
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjective
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjectiveNiels
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Double
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByPow2
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ToMontgomery
import Curve25519Dalek.Specs.Subtle
import Curve25519Dalek.Specs.Window.Basic
import Curve25519Dalek.Specs.Window.LookupTable.From
import Curve25519Dalek.Specs.Window.LookupTable.Select

/-!
# Axioms of the ported specs

Each public spec theorem of the files ported from curve25519-dalek-lean-verify, and of
`Subtle.lean` and `Window/Basic.lean`, depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. `#guard_msgs` checks this, so the build fails if a
spec depends on another axiom, for example on the `sorry` in the associativity of the
upstream point group.
-/

/-- info: 'curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_select_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg_spec

/-- info: 'curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint.neg_spec

/-- info: 'curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint.add_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_extended_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_extended_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_projective_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.CompletedPoint.as_projective_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_point

/-- info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_assign_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_select_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec

/-- info: 'curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint.neg_spec

/-- info: 'curve25519_dalek.backend.serial.curve_models.ProjectivePoint.double_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.curve_models.ProjectivePoint.double_spec

/-- info: 'curve25519_dalek.backend.serial.u64.constants.EDWARDS_D2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.constants.EDWARDS_D2_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_select_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.from_limbs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.from_limbs_spec

/-- info: 'curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.ONE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.ONE_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.square2_loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.square2_loop_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.square2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.square2_spec

/-- info: 'curve25519_dalek.backend.serial.u64.field.FieldElement51.ZERO_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.backend.serial.u64.field.FieldElement51.ZERO_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.as_affine_niels_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.as_affine_niels_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.as_projective_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.as_projective_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.as_projective_niels_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.as_projective_niels_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.double_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.double_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.mul_by_pow_2_loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.mul_by_pow_2_loop_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.mul_by_pow_2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.mul_by_pow_2_spec

/-- info: 'curve25519_dalek.edwards.EdwardsPoint.to_montgomery_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.edwards.EdwardsPoint.to_montgomery_spec

/-- info: 'curve25519_dalek.U16.Insts.SubtleConstantTimeEq.ct_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.U16.Insts.SubtleConstantTimeEq.ct_eq_spec

/-- info: 'curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_assign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_assign_spec

/-- info: 'curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_select_spec

/-- info: 'curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable.next_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable.next_spec

/-- info: 'curve25519_dalek.window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_loop_spec

/-- info: 'curve25519_dalek.window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.window.LookupTableProjectiveNielsPoint.Insts.CoreConvertFromSharedAEdwardsPoint.from_spec

/-- info: 'curve25519_dalek.window.LookupTable.select_loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.window.LookupTable.select_loop_spec

/-- info: 'curve25519_dalek.window.LookupTable.select_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms curve25519_dalek.window.LookupTable.select_spec
