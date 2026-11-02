import Sim.Field
import Sim.Bytes

/-! # Constants

dalek stores `EDWARDS_D`, `SQRT_M1` and `INVSQRT_A_MINUS_D` as five limbs. The reference port
stores the same constants as 32 little-endian bytes, copied from hacspec. Both give the same
natural number below `p`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace RistrettoSim

/-- The value of `d = -121665/121666`. -/
def nD : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
/-- The value of `sqrt(-1)`. -/
def nSqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752
/-- The value of `1/sqrt(a - d)`. -/
def nInvsqrtAMinusD : Nat :=
  54469307008909316920995813868745141605393597292927456921205312896311721017578

theorem edwards_d_spec :
    backend.serial.u64.constants.EDWARDS_D ⦃ r => toZ r = ((nD : Nat) : ZMod p) ∧ Bnd 51 r ⦄ := by
  unfold backend.serial.u64.constants.EDWARDS_D backend.serial.u64.field.FieldElement51.from_limbs
  rw [spec_ok]
  refine ⟨?_, fun i hi => by interval_cases i <;> decide⟩
  simp only [toZ]
  congr 1

theorem sqrt_m1_spec :
    backend.serial.u64.constants.SQRT_M1 ⦃ r => toZ r = ((nSqrtM1 : Nat) : ZMod p) ∧ Bnd 51 r ⦄ := by
  unfold backend.serial.u64.constants.SQRT_M1 backend.serial.u64.field.FieldElement51.from_limbs
  rw [spec_ok]
  refine ⟨?_, fun i hi => by interval_cases i <;> decide⟩
  simp only [toZ]
  congr 1

theorem invsqrt_a_minus_d_spec :
    backend.serial.u64.constants.INVSQRT_A_MINUS_D
      ⦃ r => toZ r = ((nInvsqrtAMinusD : Nat) : ZMod p) ∧ Bnd 51 r ⦄ := by
  unfold backend.serial.u64.constants.INVSQRT_A_MINUS_D
    backend.serial.u64.field.FieldElement51.from_limbs
  rw [spec_ok]
  refine ⟨?_, fun i hi => by interval_cases i <;> decide⟩
  simp only [toZ]
  congr 1

theorem one_spec :
    backend.serial.u64.field.FieldElement51.ONE ⦃ r => toZ r = 1 ∧ Bnd 51 r ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.ONE
    backend.serial.u64.field.FieldElement51.from_limbs
  rw [spec_ok]
  refine ⟨?_, fun i hi => by interval_cases i <;> decide⟩
  simp only [toZ]
  rw [show Field51_as_Nat (Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 1 by decide]
  rfl

theorem ref_d : ristretto_ref.d = ok ((nD : Nat) : _root_.field.Fe) := by
  unfold ristretto_ref.d
  rw [fe_from_bytes_eq]
  congr 2

theorem ref_sqrt_m1 : ristretto_ref.sqrt_m1 = ok ((nSqrtM1 : Nat) : _root_.field.Fe) := by
  unfold ristretto_ref.sqrt_m1
  rw [fe_from_bytes_eq]
  congr 2

theorem ref_invsqrt_a_minus_d :
    ristretto_ref.invsqrt_a_minus_d = ok ((nInvsqrtAMinusD : Nat) : _root_.field.Fe) := by
  unfold ristretto_ref.invsqrt_a_minus_d
  rw [fe_from_bytes_eq]
  congr 2

end RistrettoSim
