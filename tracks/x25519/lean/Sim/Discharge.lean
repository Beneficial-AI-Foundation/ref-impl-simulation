import Sim.Pilot
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square

/-! # The field contracts of the pilot are proved

Each contract of `FieldContracts` is the ported curve25519-dalek-lean-verify theorem
(`add_spec`, `sub_spec`, `mul_spec`, `square_spec`, built on Aeneas d119a474). With all four,
the ladder step theorem holds with only the limb-bound premises. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek

namespace X25519Sim

open DalekSim

theorem add_contract_holds (a b : FE) (ha : Bnd 53 a) (hb : Bnd 53 b) :
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b
      ⦃ r => (∀ i < 5, (r[i]!).val = (a[i]!).val + (b[i]!).val) ∧ Bnd 54 r ⦄ :=
  Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec a b ha hb

theorem sub_contract_holds (a b : FE) (ha : Bnd 63 a) (hb : Bnd 54 b) :
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub a b
      ⦃ r => Bnd 52 r ∧ (Field51_as_Nat r + Field51_as_Nat b) % p = Field51_as_Nat a % p ⦄ :=
  Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec a b ha hb

theorem mul_contract_holds (a b : FE) (ha : Bnd 54 a) (hb : Bnd 54 b) :
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul a b
      ⦃ r => Field51_as_Nat r ≡ Field51_as_Nat a * Field51_as_Nat b [MOD p] ∧ Bnd 52 r ⦄ :=
  Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec a b ha hb

theorem square_contract_holds (a : FE) (ha : Bnd 54 a) :
    backend.serial.u64.field.FieldElement51.square a
      ⦃ r => Field51_as_Nat r ≡ Field51_as_Nat a ^ 2 [MOD p] ∧ Bnd 52 r ⦄ :=
  backend.serial.u64.field.FieldElement51.square_spec a ha

/-- All four field contracts hold. -/
theorem field_contracts : FieldContracts :=
  ⟨add_contract_holds, sub_contract_holds, mul_contract_holds, square_contract_holds⟩

/-- The ladder step theorem with the field contracts discharged. Only the limb bounds on the
inputs stay as premises. -/
theorem differential_add_and_double_refines_proved
    (P Q : montgomery.ProjectivePoint) (u : FE)
    (hPU : Bnd 53 P.U) (hPW : Bnd 53 P.W) (hQU : Bnd 53 Q.U) (hQW : Bnd 53 Q.W)
    (hu : Bnd 54 u) (z1 : _root_.field.Fe) :
    montgomery.differential_add_and_double P Q u ⦃ r =>
      ∃ s, x25519_ref.point_add_and_double (toZ u, z1)
              ((toZ P.U, toZ P.W), (toZ Q.U, toZ Q.W)) = ok s ∧
        toZ r.1.U = s.1.1 ∧ toZ r.1.W = s.1.2 ∧
        toZ r.2.U = s.2.1 ∧ toZ r.2.W = s.2.2 ∧
        Bnd 52 r.1.U ∧ Bnd 52 r.1.W ∧ Bnd 52 r.2.U ∧ Bnd 52 r.2.W ⦄ :=
  differential_add_and_double_refines field_contracts P Q u hPU hPW hQU hQW hu z1

end X25519Sim
