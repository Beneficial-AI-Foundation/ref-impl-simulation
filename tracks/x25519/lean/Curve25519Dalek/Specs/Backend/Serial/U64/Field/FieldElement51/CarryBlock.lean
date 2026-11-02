/-
Written for ref-impl-simulation track B (Aeneas d119a474).
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Auxiliary

/-! # One carry step of the radix-2⁵¹ carry chain

`pow2k` and `mul` both propagate carries through five 128-bit accumulators with the same
seven operations per limb. `carry_block` is that block. Its spec lets the two carry stages
(`carry_prop_stage` in `Pow2K.lean`, `mul_carry_prop_stage` in `Mul.lean`) step over a block
with one call, so that each proof stays within the default heartbeats.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- One carry block: add the carry of `cprev` to `cnext` and store the low 51 bits of `cprev`
at index `k`. -/
def carry_block (a : Array U64 5#usize) (k : Usize) (cprev cnext : U128) (mask : U64) :
    Result (Array U64 5#usize × U128) := do
  let s ← cprev >>> 51#i32
  let s1 ← lift (UScalar.cast .U64 s)
  let s2 ← lift (UScalar.cast .U128 s1)
  let c ← cnext + s2
  let t ← lift (UScalar.cast .U64 cprev)
  let t1 ← lift (t &&& mask)
  let a' ← Array.update a k t1
  ok (a', c)

/-- The carry `cprev / 2 ^ 51` survives the casts to `U64` and back. -/
theorem carry_cast (cprev s : U128) (s1 : U64) (s2 : U128) (hp : cprev.val < 2 ^ 115)
    (hs : s.val = cprev.val >>> 51) (h1 : s1 = UScalar.cast .U64 s)
    (h2 : s2 = UScalar.cast .U128 s1) : s2.val = cprev.val / 2 ^ 51 := by
  subst h1 h2
  simp only [UScalar.cast_val_eq, UScalarTy.numBits, hs, Nat.shiftRight_eq_div_pow]
  exact double_cast_of_lt _ (carry_fits_U64 _ hp)

/-- Masking the `U64` cast of `cprev` gives its low 51 bits. -/
theorem low_bits (cprev : U128) (t t1 mask : U64) (hm : mask.val = 2 ^ 51 - 1)
    (ht : t = UScalar.cast .U64 cprev) (h1 : t1.val = (t &&& mask).val) :
    t1.val = cprev.val % 2 ^ 51 := by
  subst ht
  rw [h1, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod, UScalar.cast_val_eq]
  simp only [UScalarTy.numBits]
  exact Nat.mod_mod_of_dvd _ (by norm_num)

@[step]
theorem carry_block_spec (a : Array U64 5#usize) (k : Usize) (cprev cnext : U128) (mask : U64)
    (hk : k.val < 5) (hm : mask.val = 2 ^ 51 - 1) (hp : cprev.val < 2 ^ 115)
    (hn : cnext.val + cprev.val / 2 ^ 51 < 2 ^ 128) :
    carry_block a k cprev cnext mask ⦃ r =>
      r.2.val = cnext.val + cprev.val / 2 ^ 51 ∧
      r.1[k.val]!.val = cprev.val % 2 ^ 51 ∧
      ∀ j, j ≠ k.val → r.1[j]! = a[j]! ⦄ := by
  unfold carry_block
  step*
  · rw [carry_cast cprev s s1 s2 hp s_post s1_post s2_post]
    scalar_tac
  · refine ⟨?_, ?_, ?_⟩
    · rw [c_post, carry_cast cprev s s1 s2 hp s_post s1_post s2_post]
    · rw [a'_post, Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simp [hk]⟩]
      exact low_bits cprev t t1 mask hm t_post t1_post
    · intro j hj
      rw [a'_post, Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm hj)]

end curve25519_dalek.backend.serial.u64.field.FieldElement51
