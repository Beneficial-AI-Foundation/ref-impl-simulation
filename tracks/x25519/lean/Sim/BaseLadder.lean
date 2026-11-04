import Sim.X25519
import Sim.EdwardsLadder

/-! # The ladder at `u = 9` on a 32-byte scalar

`enc_ladder_nine_clamped`: for a scalar `k` with bit 255 cleared, as clamping leaves it, the
ladder at `u = 9` over bits 254 down to 0 of `k` returns `toU` of `k • B` on edwards25519.
`dalekLadder_basepoint` and `mul_basepoint_spec` state the same for dalek's ladder on
`X25519_BASEPOINT_BYTES`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open X25519Sim.LadderMath X25519Sim.EdwardsBridge X25519Sim.EdwardsLadder DalekSim
  DalekSim.Edwards

namespace X25519Sim

/-! ## The number of a list of bits -/

/-- Start values add `n 2^len` to the number. -/
theorem bitsVal_eq (n : ℕ) (bits : List Bool) :
    bitsVal n bits = n * 2 ^ bits.length + bitsVal 0 bits := by
  induction bits generalizing n with
  | nil => simp
  | cons b bits ih =>
    rw [bitsVal_cons, bitsVal_cons, ih, ih (2 * 0 + b.toNat), List.length_cons, pow_succ]
    ring

/-- Reading `l1 ++ l2` reads `l1`, then `l2`. -/
theorem bitsVal_append (n : ℕ) (l1 l2 : List Bool) :
    bitsVal n (l1 ++ l2) = bitsVal (bitsVal n l1) l2 :=
  List.foldl_append ..

/-- The number of `len` bits is below `2^len`. -/
theorem bitsVal_lt (bits : List Bool) : bitsVal 0 bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
    rw [bitsVal_cons, bitsVal_eq, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- `bitsFrom k n` has `n` bits. -/
theorem length_bitsFrom (k : Array U8 32#usize) (n : ℕ) : (bitsFrom k n).length = n := by
  simp [bitsFrom]

/-- `bitsFrom k (n + j)` is bits `n + j - 1` down to `n`, then `bitsFrom k n`. -/
theorem bitsFrom_add (k : Array U8 32#usize) (n j : ℕ) :
    bitsFrom k (n + j) = (List.range j).reverse.map (fun i => kbit k (n + i)) ++ bitsFrom k n := by
  induction j with
  | zero => simp
  | succ j ih => rw [← add_assoc, bitsFrom_succ, ih, List.range_succ]; simp

/-- The 8 bits of a byte, most significant first, give the byte. -/
theorem byte_bits : ∀ v < 256,
    bitsVal 0 ((List.range 8).reverse.map (fun i => (v >>> i) % 2 == 1)) = v := by
  decide +kernel

/-- Bit `8 m + i` of `k` is bit `i` of byte `m`. -/
theorem kbit_byte (k : Array U8 32#usize) (m i : ℕ) (hi : i < 8) :
    kbit k (8 * m + i) = ((k.val[m]!.val >>> i) % 2 == 1) := by
  unfold kbit
  rw [show (8 * m + i) / 8 = m by omega, show (8 * m + i) % 8 = i by omega]

/-- The low `8 m` bits of `k` give its first `m` bytes as a little-endian number. -/
theorem bitsVal_bitsFrom_bytes (k : Array U8 32#usize) (m : ℕ) :
    bitsVal 0 (bitsFrom k (8 * m)) = ∑ i ∈ Finset.range m, 2 ^ (8 * i) * (k.val[i]!).val := by
  induction m with
  | zero => simp [bitsFrom]
  | succ m ih =>
    have hb : (List.range 8).reverse.map (fun i => kbit k (8 * m + i)) =
        (List.range 8).reverse.map (fun i => (k.val[m]!.val >>> i) % 2 == 1) :=
      List.map_congr_left (fun i hi => kbit_byte k m i (by simpa using hi))
    rw [show 8 * (m + 1) = 8 * m + 8 by ring, bitsFrom_add, bitsVal_append, bitsVal_eq,
      length_bitsFrom, ih, Finset.sum_range_succ, hb, byte_bits _ (U8.lt_succ_max _)]
    ring

/-- `k` is bit 255 times `2²⁵⁵` plus the number of bits 254 down to 0. -/
theorem U8x32_as_Nat_bits (k : Array U8 32#usize) :
    U8x32_as_Nat k = (kbit k 255).toNat * 2 ^ 255 + bitsVal 0 (bitsFrom k 255) := by
  have h : bitsVal 0 (bitsFrom k (8 * 32)) = U8x32_as_Nat k := by
    rw [bitsVal_bitsFrom_bytes, U8x32_as_Nat]
    simp only [Array.getElem!_Nat_eq]
  rw [← h, show 8 * 32 = 255 + 1 from rfl, bitsFrom_succ, bitsVal_cons, bitsVal_eq,
    length_bitsFrom]
  simp

/-- Bits 254 down to 0 of `k` give `k mod 2²⁵⁵`. -/
theorem bitsVal_bitsFrom_255 (k : Array U8 32#usize) :
    bitsVal 0 (bitsFrom k 255) = U8x32_as_Nat k % 2 ^ 255 := by
  have hl := bitsVal_lt (bitsFrom k 255)
  rw [length_bitsFrom] at hl
  rw [U8x32_as_Nat_bits, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- If bit 255 of `k` is 0, then bits 254 down to 0 give `k`. -/
theorem bitsVal_bitsFrom_255_of_lt (k : Array U8 32#usize) (hk : (k.val[31]!).val < 128) :
    bitsVal 0 (bitsFrom k 255) = U8x32_as_Nat k := by
  rw [U8x32_as_Nat_bits, kbit_255 k hk]
  simp

/-! ## The ladder at `u = 9` -/

/-- For every 32-byte `k`, the ladder at `u = 9` over bits 254 down to 0 of `k` returns
`toU` of `(k mod 2²⁵⁵) • B`. -/
theorem enc_ladder_nine_bytes (k : Array U8 32#usize) :
    enc (ladder (9 : ZMod p) (bitsFrom k 255) ((1, 0), (9, 1))).1 =
      toU ((U8x32_as_Nat k % 2 ^ 255) • basePoint).1.2 := by
  rw [enc_ladder_nine, bitsVal_bitsFrom_255]

/-- **The ladder at `u = 9` computes the public key.** If bit 255 of `k` is 0, as after
clamping, the ladder at `u = 9` over bits 254 down to 0 of `k` returns `toU` of `k • B`. -/
theorem enc_ladder_nine_clamped (k : Array U8 32#usize) (hk : (k.val[31]!).val < 128) :
    enc (ladder (9 : ZMod p) (bitsFrom k 255) ((1, 0), (9, 1))).1 =
      toU (U8x32_as_Nat k • basePoint).1.2 := by
  rw [enc_ladder_nine, bitsVal_bitsFrom_255_of_lt k hk]

/-! ## dalek's ladder on `X25519_BASEPOINT_BYTES` -/

/-- `X25519_BASEPOINT_BYTES` decodes to `u = 9`. -/
theorem decodeU_basepoint : decodeU x25519_dalek.x25519.X25519_BASEPOINT_BYTES = 9 := by
  have h : U8x32_as_Nat x25519_dalek.x25519.X25519_BASEPOINT_BYTES % 2 ^ 255 = 9 := by
    unfold x25519_dalek.x25519.X25519_BASEPOINT_BYTES
    decide +kernel
  unfold decodeU
  rw [h]
  rfl

/-- dalek's ladder on `X25519_BASEPOINT_BYTES` and a scalar with bit 255 cleared returns the
point whose encoding is `toU` of `k • B`. -/
theorem dalekLadder_basepoint (k : Array U8 32#usize) (hk : (k.val[31]!).val < 128) :
    enc (K := ZMod p) (dalekLadder x25519_dalek.x25519.X25519_BASEPOINT_BYTES k).1 =
      toU (U8x32_as_Nat k • basePoint).1.2 := by
  rw [dalekLadder, decodeU_basepoint]
  exact enc_ladder_nine_clamped k hk

/-- dalek's `&MontgomeryPoint * &Scalar` on `X25519_BASEPOINT_BYTES` and a scalar `k` with bit
255 cleared returns the bytes of `toU` of `k • B`. -/
theorem mul_basepoint_spec (k : Array U8 32#usize) (hk : (k.val[31]!).val < 128) :
    curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul
      x25519_dalek.x25519.X25519_BASEPOINT_BYTES ⟨k⟩ ⦃ r =>
      _root_.field.fe_to_bytes (toU (F := ZMod p) (U8x32_as_Nat k • basePoint).1.2) = ok r ⦄ := by
  apply spec_mono (mul_spec _ k)
  intro r hr
  rw [← hr]
  exact congrArg _root_.field.fe_to_bytes (dalekLadder_basepoint k hk).symm

end X25519Sim
