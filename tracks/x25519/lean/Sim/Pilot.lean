import X25519Ref.Funs
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Auxiliary

/-! # Pilot: one Montgomery ladder step, real against reference

Real: `curve25519_dalek::montgomery::differential_add_and_double` (FieldElement51, u64 limbs).
Reference: `x25519_ref::point_add_and_double`, a hand port of the hacspec RFC 7748 spec, over
the field model `ZMod (2^255 - 19)`.

Relation: a `FieldElement51` represents the field element `toZ f = Field51_as_Nat f mod p`.

The field operation contracts (`FieldContracts`) are the statements of the
curve25519-dalek-lean-verify theorems `add_spec`, `sub_spec`, `mul_spec`, `square_spec`, in the
form those theorems have. They are a premise here. `Sim/Discharge.lean` proves all four with the
ported proofs (Aeneas d119a474) and states the corollary `differential_add_and_double_refines_proved`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace X25519Sim

abbrev FE := backend.serial.u64.field.FieldElement51

/-- The representation relation: limbs to the reference field. -/
def toZ (f : FE) : _root_.field.Fe := ((Field51_as_Nat f : Nat) : ZMod p)

/-- Every limb is below `2 ^ k`. -/
def Bnd (k : Nat) (f : FE) : Prop := ∀ i < 5, (f[i]!).val < 2 ^ k

/-- The four field operation contracts used by the ladder step, as proved upstream. -/
structure FieldContracts : Prop where
  add : ∀ a b : FE, Bnd 53 a → Bnd 53 b →
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b
      ⦃ r => (∀ i < 5, (r[i]!).val = (a[i]!).val + (b[i]!).val) ∧ Bnd 54 r ⦄
  sub : ∀ a b : FE, Bnd 63 a → Bnd 54 b →
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub a b
      ⦃ r => Bnd 52 r ∧ (Field51_as_Nat r + Field51_as_Nat b) % p = Field51_as_Nat a % p ⦄
  mul : ∀ a b : FE, Bnd 54 a → Bnd 54 b →
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul a b
      ⦃ r => Field51_as_Nat r ≡ Field51_as_Nat a * Field51_as_Nat b [MOD p] ∧ Bnd 52 r ⦄
  square : ∀ a : FE, Bnd 54 a →
    backend.serial.u64.field.FieldElement51.square a
      ⦃ r => Field51_as_Nat r ≡ Field51_as_Nat a ^ 2 [MOD p] ∧ Bnd 52 r ⦄

theorem bnd_mono {j k : Nat} {f : FE} (h : Bnd j f) (hjk : j ≤ k) : Bnd k f :=
  fun i hi => lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by norm_num) hjk)

/-- The constant `(A + 2) / 4 = 121666`. -/
theorem aplus2_over_four_eq :
    backend.serial.u64.constants.APLUS2_OVER_FOUR =
      ok (Array.make 5#usize [121666#u64, 0#u64, 0#u64, 0#u64, 0#u64]) := by
  unfold backend.serial.u64.constants.APLUS2_OVER_FOUR
  rfl

theorem aplus2_bnd : Bnd 54 (Array.make 5#usize [121666#u64, 0#u64, 0#u64, 0#u64, 0#u64]) := by
  intro i hi
  interval_cases i <;> decide

theorem aplus2_nat :
    Field51_as_Nat (Array.make 5#usize [121666#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 121666 := by
  decide

theorem aplus2_z : toZ (Array.make 5#usize [121666#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 121666 := by
  simp only [toZ, aplus2_nat]
  rfl

theorem aplus2_spec :
    backend.serial.u64.constants.APLUS2_OVER_FOUR ⦃ r => toZ r = 121666 ∧ Bnd 54 r ⦄ := by
  rw [aplus2_over_four_eq, spec_ok]
  exact ⟨aplus2_z, aplus2_bnd⟩

/-- The reference ladder step in closed form. It is total. -/
theorem point_add_and_double_eq (x1 z1 x2 z2 x3 z3 : _root_.field.Fe) :
    x25519_ref.point_add_and_double (x1, z1) ((x2, z2), (x3, z3)) =
      ok (((x2 + z2) ^ 2 * ((x2 - z2) * (x2 - z2)),
           ((x2 + z2) ^ 2 - (x2 - z2) * (x2 - z2)) *
             ((x2 + z2) ^ 2 + 121665 * ((x2 + z2) ^ 2 - (x2 - z2) * (x2 - z2)))),
          (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) ^ 2,
           x1 * ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) ^ 2)) := by
  simp only [x25519_ref.point_add_and_double, _root_.field.fe_add, _root_.field.fe_sub,
    _root_.field.fe_mul, _root_.field.fe_sq, _root_.field.fe_lit, bind_ok]
  congr 3

section
variable (C : FieldContracts)
include C

/-! Contracts restated over `toZ`. This is the representation step: it is the same for every
field function pair and a generator can emit it from the contract table. -/

theorem add_z (a b : FE) (ha : Bnd 53 a) (hb : Bnd 53 b) :
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b
      ⦃ r => toZ r = toZ a + toZ b ∧ Bnd 54 r ⦄ := by
  apply spec_mono (C.add a b ha hb)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  simp only [toZ, pointwise_add_Field51_as_Nat a b r h1, Nat.cast_add]
  rfl

theorem sub_z (a b : FE) (ha : Bnd 63 a) (hb : Bnd 54 b) :
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub a b
      ⦃ r => toZ r = toZ a - toZ b ∧ Bnd 52 r ⦄ := by
  apply spec_mono (C.sub a b ha hb)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h1⟩
  have : ((Field51_as_Nat r + Field51_as_Nat b : Nat) : ZMod p) = ((Field51_as_Nat a : Nat) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h2
  simp only [toZ]
  push_cast at this
  exact eq_sub_of_add_eq this

theorem mul_z (a b : FE) (ha : Bnd 54 a) (hb : Bnd 54 b) :
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul a b
      ⦃ r => toZ r = toZ a * toZ b ∧ Bnd 52 r ⦄ := by
  apply spec_mono (C.mul a b ha hb)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact this

theorem square_z (a : FE) (ha : Bnd 54 a) :
    backend.serial.u64.field.FieldElement51.square a
      ⦃ r => toZ r = toZ a ^ 2 ∧ Bnd 52 r ⦄ := by
  apply spec_mono (C.square a ha)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact this

/-- **Pilot simulation theorem.** One ladder step of curve25519-dalek refines one ladder step of
the RFC 7748 reference, under the limb relation `toZ`, given the limb bound invariant. -/
theorem differential_add_and_double_refines
    (P Q : montgomery.ProjectivePoint) (u : FE)
    (hPU : Bnd 53 P.U) (hPW : Bnd 53 P.W) (hQU : Bnd 53 Q.U) (hQW : Bnd 53 Q.W)
    (hu : Bnd 54 u) (z1 : _root_.field.Fe) :
    montgomery.differential_add_and_double P Q u ⦃ r =>
      ∃ s, x25519_ref.point_add_and_double (toZ u, z1)
              ((toZ P.U, toZ P.W), (toZ Q.U, toZ Q.W)) = ok s ∧
        toZ r.1.U = s.1.1 ∧ toZ r.1.W = s.1.2 ∧
        toZ r.2.U = s.2.1 ∧ toZ r.2.W = s.2.2 ∧
        Bnd 52 r.1.U ∧ Bnd 52 r.1.W ∧ Bnd 52 r.2.U ∧ Bnd 52 r.2.W ⦄ := by
  unfold montgomery.differential_add_and_double
  -- lockstep part: one contract per real call, bounds discharged by `bnd_mono`
  step with add_z C as ⟨t0, h0, b0⟩
  step with sub_z C as ⟨t1, h1, b1⟩
  · exact bnd_mono hPU (by norm_num)
  · exact bnd_mono hPW (by norm_num)
  step with add_z C as ⟨t2, h2, b2⟩
  step with sub_z C as ⟨t3, h3, b3⟩
  · exact bnd_mono hQU (by norm_num)
  · exact bnd_mono hQW (by norm_num)
  step with square_z C as ⟨t4, h4, b4⟩
  step with square_z C as ⟨t5, h5, b5⟩
  · exact bnd_mono b1 (by norm_num)
  step with sub_z C as ⟨t6, h6, b6⟩
  · exact bnd_mono b4 (by norm_num)
  · exact bnd_mono b5 (by norm_num)
  step with mul_z C as ⟨t7, h7, b7⟩
  · exact bnd_mono b3 (by norm_num)
  step with mul_z C as ⟨t8, h8, b8⟩
  · exact bnd_mono b1 (by norm_num)
  step with add_z C as ⟨t9, h9, b9⟩
  · exact bnd_mono b7 (by norm_num)
  · exact bnd_mono b8 (by norm_num)
  step with sub_z C as ⟨t10, h10, b10⟩
  · exact bnd_mono b7 (by norm_num)
  · exact bnd_mono b8 (by norm_num)
  step with square_z C as ⟨t11, h11, b11⟩
  step with square_z C as ⟨t12, h12, b12⟩
  · exact bnd_mono b10 (by norm_num)
  step with aplus2_spec as ⟨fe, hfe, bfe⟩
  step with mul_z C as ⟨t13, h13, b13⟩
  · exact bnd_mono b6 (by norm_num)
  step with mul_z C as ⟨t14, h14, b14⟩
  · exact bnd_mono b4 (by norm_num)
  · exact bnd_mono b5 (by norm_num)
  step with add_z C as ⟨t15, h15, b15⟩
  · exact bnd_mono b13 (by norm_num)
  · exact bnd_mono b5 (by norm_num)
  step with mul_z C as ⟨t16, h16, b16⟩
  · exact bnd_mono b6 (by norm_num)
  step with mul_z C as ⟨t17, h17, b17⟩
  · exact bnd_mono b12 (by norm_num)
  -- the reference side is total: compute it
  refine ⟨_, point_add_and_double_eq _ _ _ _ _ _, ?_, ?_, ?_, ?_, b14, b16, b11, b17⟩
  -- representation part: ring identities in ZMod p
  · -- x_2 = AA * BB  (real squares B, the reference multiplies B * B)
    rw [h14, h4, h5, h0, h1]; ring
  · -- z_2: real E * (121666 E + BB), reference E * (AA + 121665 E); equal since AA = BB + E
    rw [h16, h15, h13, hfe, h6, h4, h5, h0, h1]; ring
  · -- x_3 = (DA + CB)^2  (real computes A * D and B * C)
    rw [h11, h9, h7, h8, h0, h1, h2, h3]; ring
  · -- z_3 = x_1 * (DA - CB)^2
    rw [h17, h12, h10, h7, h8, h0, h1, h2, h3]; ring

end
end X25519Sim
