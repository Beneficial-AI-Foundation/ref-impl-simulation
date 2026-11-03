import Sim.RealSide
import Sim.Bytes

/-! # Full refinement: dalek's `mul_clamped` against the reference `x25519_scalarmult`

`mul_clamped_refines` states that, for every 32-byte scalar `s` and u-coordinate `u`, the real
`MontgomeryPoint::mul_clamped u s` returns without panic, overflow or divergence, and that
the reference `x25519_scalarmult s u` returns the same bytes. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
open X25519Sim.LadderMath

namespace X25519Sim

open DalekSim

/-! ## Clamping -/

/-- dalek's `clamp_integer` is the reference `mask_scalar`: the code is the same. -/
theorem clamp_eq_mask (s : Array U8 32#usize) :
    scalar.clamp_integer s = x25519_ref.mask_scalar s := rfl

/-- The masked scalar has bit 255 cleared: byte 31 is below 128. -/
theorem mask_scalar_spec (s : Array U8 32#usize) :
    x25519_ref.mask_scalar s ⦃ k => (k.val[31]!).val < 128 ⦄ := by
  unfold x25519_ref.mask_scalar
  step*
  have hk : k.val[31]! = i5 := by
    rw [k_post, Array.set_val_eq, getElem!_pos _ 31 (by simp)]; simp
  have h4 : i4 = i3 := by rw [i4_post, s2_post]; simp [Array.set_val_eq]
  have h3 : i3.val < 128 := by
    rw [i3_post, UScalar.val_and]; have := Nat.and_le_right (n := i2.val) (m := (127#u8).val)
    simp at this ⊢; omega
  rw [hk, i5_post, UScalar.val_or, h4]
  exact Nat.or_lt_two_pow (n := 7) h3 (by simp)

/-- If byte 31 is below 128, then bit 255 is 0. -/
theorem kbit_255 (k : Array U8 32#usize) (h : (k.val[31]!).val < 128) : kbit k 255 = false := by
  unfold kbit
  have h' : (k.val[31]!).val >>> 7 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by omega)
  rw [show 255 / 8 = 31 from rfl, show 255 % 8 = 7 from rfl, h']
  rfl

/-! ## Decoding -/

/-- The u-coordinate both sides decode, as a reference field element. -/
def decodeU (u : Array U8 32#usize) : _root_.field.Fe :=
  ((U8x32_as_Nat u % 2 ^ 255 : ℕ) : ZMod _root_.field.p)

/-- `decode_point u` returns `(decodeU u, 1)`. -/
theorem decode_point_spec (u : Array U8 32#usize) :
    x25519_ref.decode_point u ⦃ r => r = (decodeU u, 1) ⦄ := by
  unfold x25519_ref.decode_point
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, _⟩
  step as ⟨u1, hu1⟩
  rw [fe_from_bytes_eq]
  simp only [bind_ok, fe_lit_one]
  have hx : i1.val = (u.val[31]!).val % 128 := by
    rw [hi1, UScalar.val_and, hi, getElem!_pos u.val 31 (by simp)]
    exact land_pow_two_sub_one_eq_mod _ 7
  rw [hu1, U8x32_mask_top u i1 hx]
  exact (spec_ok _).mpr rfl

/-- `FieldElement51::from_bytes u` represents `decodeU u`, with limbs below `2 ^ 51`. -/
theorem from_bytes_z (u : Array U8 32#usize) :
    backend.serial.u64.field.FieldElement51.from_bytes u ⦃ r => toZ r = decodeU u ∧ Bnd 51 r ⦄ := by
  apply spec_mono (backend.serial.u64.field.FieldElement51.from_bytes_spec u)
  rintro r ⟨h1, h2⟩
  exact ⟨(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1, h2⟩

/-! ## Encoding -/

/-- The `invert_spec` postcondition gives `toZ inv = (toZ w)⁻¹` in `ZMod p`, with `0⁻¹ = 0`. -/
theorem toZ_inv (w inv : FE)
    (hnz : Field51_as_Nat w % p ≠ 0 → (Field51_as_Nat inv % p * (Field51_as_Nat w % p)) % p = 1)
    (hz : Field51_as_Nat w % p = 0 → Field51_as_Nat inv % p = 0) :
    toZ inv = (toZ w)⁻¹ := by
  show ((Field51_as_Nat inv : ℕ) : ZMod p) = ((Field51_as_Nat w : ℕ) : ZMod p)⁻¹
  by_cases h0 : Field51_as_Nat w % p = 0
  · have hw : ((Field51_as_Nat w : ℕ) : ZMod p) = 0 := by
      rw [← ZMod.natCast_mod, h0, Nat.cast_zero]
    have hi : ((Field51_as_Nat inv : ℕ) : ZMod p) = 0 := by
      rw [← ZMod.natCast_mod, hz h0, Nat.cast_zero]
    rw [hw, hi, inv_zero]
  · have h1 := congrArg (fun n : ℕ => (n : ZMod p)) (hnz h0)
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at h1
    exact eq_inv_of_mul_eq_one_left h1

/-- For limbs below `2 ^ 52`, `as_affine P` terminates and returns
`fe_to_bytes (toZ P.U * (toZ P.W)⁻¹)`, the canonical encoding of `U / W`. -/
theorem as_affine_spec (P : montgomery.ProjectivePoint) (hP : BndP P) :
    montgomery.ProjectivePoint.as_affine P ⦃ r =>
      _root_.field.fe_to_bytes (toZ P.U * (toZ P.W)⁻¹) = ok r ⦄ := by
  unfold montgomery.ProjectivePoint.as_affine
  have hW : ∀ i < 5, (P.W[i]!).val < 2 ^ 54 := bnd_mono hP.2 (by norm_num)
  step with field.FieldElement51.invert_spec P.W hW as ⟨inv, hnz, hz, hib⟩
  step with mul_z field_contracts P.U inv (bnd_mono hP.1 (by norm_num)) (bnd_mono hib (by norm_num))
    as ⟨m, hm, hmb⟩
  step with backend.serial.u64.field.FieldElement51.to_bytes_spec m as ⟨b, hb1, hb2⟩
  apply fe_to_bytes_eq
  rw [← toZ_inv P.W inv hnz hz, ← hm]
  show U8x32_as_Nat b = (((Field51_as_Nat m : ℕ) : ZMod p)).val
  rw [ZMod.val_natCast, ← hb1, Nat.mod_eq_of_lt hb2]

/-! ## The constants and the identity -/

/-- `FieldElement51::ONE` as a limb array. -/
theorem one_eq : backend.serial.u64.field.FieldElement51.ONE =
    ok (Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]) := by
  unfold backend.serial.u64.field.FieldElement51.ONE; rfl

/-- `FieldElement51::ZERO` as a limb array. -/
theorem zero_eq : backend.serial.u64.field.FieldElement51.ZERO =
    ok (Array.make 5#usize [0#u64, 0#u64, 0#u64, 0#u64, 0#u64]) := by
  unfold backend.serial.u64.field.FieldElement51.ZERO; rfl

/-- `ONE` represents 1. -/
theorem one_z : toZ (Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 1 := by
  have : Field51_as_Nat (Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 1 := by decide
  simp only [toZ, this, Nat.cast_one]; rfl

/-- `ZERO` represents 0. -/
theorem zero_z : toZ (Array.make 5#usize [0#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 0 := by
  have : Field51_as_Nat (Array.make 5#usize [0#u64, 0#u64, 0#u64, 0#u64, 0#u64]) = 0 := by decide
  simp only [toZ, this, Nat.cast_zero]; rfl

/-- `ONE` has limbs below `2 ^ 52`. -/
theorem one_bnd : Bnd 52 (Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]) := by
  intro i hi; interval_cases i <;> decide

/-- `ZERO` has limbs below `2 ^ 52`. -/
theorem zero_bnd : Bnd 52 (Array.make 5#usize [0#u64, 0#u64, 0#u64, 0#u64, 0#u64]) := by
  intro i hi; interval_cases i <;> decide


/-! ## dalek's scalar multiplication -/

/-- The dalek ladder result, from bit 254, on the decoded u-coordinate. -/
def dalekLadder (uB k : Array U8 32#usize) : Pt _root_.field.Fe × Pt _root_.field.Fe :=
  ladder (decodeU uB) (bitsFrom k 255) ((1, 0), (decodeU uB, 1))

/-- dalek's `&MontgomeryPoint * &Scalar` on the bytes `uB` and the scalar bytes `k` terminates
and returns the encoding of the first point of `dalekLadder uB k`: 255 iterations, on bits
254 down to 0 of `k`. Bit 255 of `k` is not read. -/
theorem mul_spec (uB k : Array U8 32#usize) :
    Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul uB ⟨k⟩ ⦃ r =>
      _root_.field.fe_to_bytes ((dalekLadder uB k).1.1 * (dalekLadder uB k).1.2⁻¹) = ok r ⦄ := by
  unfold Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul
  step with from_bytes_z uB as ⟨au, hau, hab⟩
  simp only [IdentityMontgomeryProjectivePoint.identity, one_eq, zero_eq, scalar.Scalar.as_bytes,
    bind_ok]
  have hx0 : BndP ⟨Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64],
      Array.make 5#usize [0#u64, 0#u64, 0#u64, 0#u64, 0#u64]⟩ := ⟨one_bnd, zero_bnd⟩
  have hx1 : BndP ⟨au, Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]⟩ :=
    ⟨bnd_mono hab (by norm_num), one_bnd⟩
  step with mul_loop_spec au (bnd_mono hab (by norm_num)) k 255 254#isize _ _ false
    (by simp) le_rfl hx0 hx1 as ⟨y0, y1, pb, hL, hb0, hb1⟩
  have hstart : toP2 (cswap false (⟨Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64],
      Array.make 5#usize [0#u64, 0#u64, 0#u64, 0#u64, 0#u64]⟩,
      ⟨au, Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]⟩)) =
      (((1 : _root_.field.Fe), (0 : _root_.field.Fe)), (decodeU uB, (1 : _root_.field.Fe))) := by
    simp only [cswap, toP2, toP, one_z, zero_z, hau, Bool.false_eq_true, if_false]
  rw [hstart, hau] at hL
  step as ⟨i, hi⟩
  step with choice_from_spec i (by rw [hi]; cases pb <;> simp) as ⟨c, hc⟩
  rw [pp_swap_eq]
  cases pb
  · have hc1 : ¬ c.val = 1#u8 := by rw [hc]; intro h; have := congrArg UScalar.val h; simp_all
    simp only [hc1, if_false, bind_ok, zeroize.Zeroize.Blanket.zeroize,
      Bool.Insts.ZeroizeDefaultIsZeroes, Bool.Insts.CoreDefaultDefault]
    simp only [core.default.DefaultBool.default, bind_ok]
    apply spec_mono (as_affine_spec y0 hb0)
    intro r hr
    rw [← hr]
    have := congrArg Prod.fst hL
    simp only [cswap, toP2, toP, Bool.false_eq_true, if_false] at this
    rw [dalekLadder, ← this]
  · have hc1 : c.val = 1#u8 := by rw [hc]; apply UScalar.eq_of_val_eq; simp [hi]
    simp only [hc1, if_true, bind_ok, zeroize.Zeroize.Blanket.zeroize,
      Bool.Insts.ZeroizeDefaultIsZeroes, Bool.Insts.CoreDefaultDefault]
    simp only [core.default.DefaultBool.default, bind_ok]
    apply spec_mono (as_affine_spec y1 hb1)
    intro r hr
    rw [← hr]
    have := congrArg Prod.fst hL
    simp only [cswap, toP2, toP, if_true] at this
    rw [dalekLadder, ← this]

/-! ## The full refinement theorem -/

/-- `4 ≠ 0` in `ZMod p`. -/
theorem four_ne_zero_zmod : (4 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  simp [p] at this

/-- **Full refinement.** For every 32-byte scalar `s` and u-coordinate `u`, dalek's
`MontgomeryPoint::mul_clamped u s` returns without panic, overflow or divergence, and the
reference `x25519_scalarmult s u` returns the same 32 bytes. -/
theorem mul_clamped_refines (u s : Array U8 32#usize) :
    montgomery.MontgomeryPoint.mul_clamped u s ⦃ r =>
      x25519_ref.x25519_scalarmult s u = ok r ⦄ := by
  obtain ⟨k, hk, hk31⟩ := exists_ok_of_spec (mask_scalar_spec s)
  unfold montgomery.MontgomeryPoint.mul_clamped
  rw [clamp_eq_mask, hk, bind_ok]
  simp only [scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint.mul,
    Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint.mul]
  apply spec_mono (mul_spec u k)
  intro r hr
  rw [← hr]
  unfold x25519_ref.x25519_scalarmult x25519_ref.decode_scalar
  rw [hk, bind_ok, eq_ok_of_spec (decode_point_spec u), bind_ok,
    eq_ok_of_spec (montgomery_ladder_eq k (decodeU u, 1)), bind_ok, encode_point_eq]
  have hbits : refBits k = false :: bitsFrom k 255 := by
    rw [refBits, bitsFrom_succ, kbit_255 k hk31]
  have hne : bitsFrom k 255 ≠ [] := by simp [bitsFrom]
  have key := enc_ladder_extra_step (K := ZMod p) (decodeU u) four_ne_zero_zmod (bitsFrom k 255) hne
  simp only [enc] at key
  rw [hbits, dalekLadder]
  exact congrArg _root_.field.fe_to_bytes key

end X25519Sim
