import RistrettoRef.Funs
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Specs.Field.FieldElement51.Pow22501
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Negate

/-! # Field operations over `toZ`

The relation of track B: a `FieldElement51` represents `toZ f = Field51_as_Nat f mod p` in the
reference field `ZMod p`. This file restates the field specs that track B ported (`add_spec`,
`sub_spec`, `mul_spec`, `square_spec`, `pow2k_spec`, `pow22501_spec`) over `toZ`, and proves
the specs of `negate` and `pow_p58`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace RistrettoSim

abbrev FE := backend.serial.u64.field.FieldElement51

/-- The value of a `FieldElement51` in the reference field: its five limbs read in radix
`2 ^ 51`, mod `p`. -/
def toZ (f : FE) : _root_.field.Fe := ((Field51_as_Nat f : Nat) : ZMod p)

/-- Every limb is below `2 ^ k`. -/
def Bnd (k : Nat) (f : FE) : Prop := ∀ i < 5, (f[i]!).val < 2 ^ k

/-- A limb bound holds for every larger exponent. -/
theorem bnd_mono {j k : Nat} {f : FE} (h : Bnd j f) (hjk : j ≤ k) : Bnd k f :=
  fun i hi => lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by norm_num) hjk)

/-- `add` with limbs below `2 ^ 53`: the sum in `ZMod p`, limbs below `2 ^ 54`. -/
theorem add_z (a b : FE) (ha : Bnd 53 a) (hb : Bnd 53 b) :
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b
      ⦃ r => toZ r = toZ a + toZ b ∧ Bnd 54 r ⦄ := by
  apply spec_mono
    (Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
      a b ha hb)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  simp only [toZ, pointwise_add_Field51_as_Nat a b r h1, Nat.cast_add]
  rfl

/-- `sub` with limbs of `a` below `2 ^ 63` and of `b` below `2 ^ 54`: the difference in
`ZMod p`, limbs below `2 ^ 52`. -/
theorem sub_z (a b : FE) (ha : Bnd 63 a) (hb : Bnd 54 b) :
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub a b
      ⦃ r => toZ r = toZ a - toZ b ∧ Bnd 52 r ⦄ := by
  apply spec_mono
    (Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
      a b ha hb)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h1⟩
  have : ((Field51_as_Nat r + Field51_as_Nat b : Nat) : ZMod p) =
      ((Field51_as_Nat a : Nat) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h2
  simp only [toZ]
  push_cast at this
  exact eq_sub_of_add_eq this

/-- `mul` with limbs below `2 ^ 54`: the product in `ZMod p`, limbs below `2 ^ 52`. -/
theorem mul_z (a b : FE) (ha : Bnd 54 a) (hb : Bnd 54 b) :
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul a b
      ⦃ r => toZ r = toZ a * toZ b ∧ Bnd 52 r ⦄ := by
  apply spec_mono
    (Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
      a b ha hb)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact this

/-- `square` with limbs below `2 ^ 54`: the square in `ZMod p`, limbs below `2 ^ 52`. -/
theorem square_z (a : FE) (ha : Bnd 54 a) :
    backend.serial.u64.field.FieldElement51.square a
      ⦃ r => toZ r = toZ a ^ 2 ∧ Bnd 52 r ⦄ := by
  apply spec_mono (backend.serial.u64.field.FieldElement51.square_spec a ha)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact this

/-- `pow2k a k` with `0 < k` and limbs below `2 ^ 54`: `a ^ (2 ^ k)` in `ZMod p`, limbs
below `2 ^ 52`. -/
theorem pow2k_z (a : FE) (k : U32) (hk : 0 < k.val) (ha : Bnd 54 a) :
    backend.serial.u64.field.FieldElement51.pow2k a k
      ⦃ r => toZ r = toZ a ^ (2 ^ k.val) ∧ Bnd 52 r ⦄ := by
  apply spec_mono (backend.serial.u64.field.FieldElement51.pow2k_spec a k hk ha)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact this

/-- `pow22501` with limbs below `2 ^ 54`: its first result is `a ^ pow22501_exp` in
`ZMod p`, with limbs below `2 ^ 52`. -/
theorem pow22501_z (a : FE) (ha : Bnd 54 a) :
    field.FieldElement51.pow22501 a
      ⦃ r => toZ r.1 = toZ a ^ field.FieldElement51.pow22501_exp ∧ Bnd 52 r.1 ⦄ := by
  apply spec_mono (field.FieldElement51.pow22501_spec a ha)
  rintro r ⟨h1, _, h3, _⟩
  refine ⟨?_, h3⟩
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact this

/-- `1 + 4 (2^250 - 1) = (p - 5) / 8`. -/
theorem p58_exp : 1 + field.FieldElement51.pow22501_exp * 2 ^ 2 = (p - 5) / 8 := by
  rw [field.FieldElement51.pow22501_exp_def]
  unfold p
  norm_num

/-- `pow_p58` computes `a ^ ((p - 5) / 8)`. -/
theorem pow_p58_z (a : FE) (ha : Bnd 54 a) :
    field.FieldElement51.pow_p58 a
      ⦃ r => toZ r = toZ a ^ ((p - 5) / 8) ∧ Bnd 52 r ⦄ := by
  unfold field.FieldElement51.pow_p58
  step with pow22501_z as ⟨t, t', ht, bt⟩
  step with pow2k_z as ⟨t20, h20, b20⟩
  · exact bnd_mono bt (by norm_num)
  step with mul_z as ⟨r, hr, br⟩
  · exact bnd_mono b20 (by norm_num)
  refine ⟨?_, br⟩
  rw [hr, h20, ht, ← pow_mul, ← pow_succ', ← p58_exp, Nat.add_comm]

/-- `negate` with limbs below `2 ^ 54`: the negation in `ZMod p`, limbs below `2 ^ 52`. -/
theorem negate_z (a : FE) (ha : Bnd 54 a) :
    backend.serial.u64.field.FieldElement51.negate a
      ⦃ r => toZ r = - toZ a ∧ Bnd 52 r ⦄ := by
  apply spec_mono (backend.serial.u64.field.FieldElement51.negate_spec a ha)
  rintro r ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have : ((Field51_as_Nat a + Field51_as_Nat r : Nat) : ZMod p) = ((0 : Nat) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  simp only [toZ]
  push_cast at this
  exact eq_neg_of_add_eq_zero_right this

/-- `Neg` on `&FieldElement51` is `negate`. -/
theorem neg_z (a : FE) (ha : Bnd 54 a) :
    Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg a
      ⦃ r => toZ r = - toZ a ∧ Bnd 52 r ⦄ := by
  unfold Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg
  exact negate_z a ha

end RistrettoSim
