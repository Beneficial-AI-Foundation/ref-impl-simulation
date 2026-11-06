import ForkSim.RefSide
import Specs.Montgomery
import Proofs.Scalar.ClampInteger
import Proofs.Helpers.AsNat

/-! # The reference X25519 is the fork's `x25519`

`x25519_scalarmult_spec`: for all 32-byte `k` and `u`, the translated reference
`x25519_scalarmult k u` returns bytes whose little-endian value is the fork's
`curve25519.x25519 (k.asNat 8) (u.asNat 8)`. `x25519_secret_to_public_spec` is the case
`u = 9`.

The proof links three pieces:

1. Track B's closed form of the reference (`ForkSim.RefSide`): the reference ladder runs
   `LadderMath.lstep` over the 256 bits of the masked scalar, from bit 255.
2. The fork's ladder (`MontgomeryModel.XZ.ladderLoop`) swaps lazily. Its state, with the
   pending swap applied, is the reference state (`toPair_ladderLoop`). So over the same bits,
   the two ladders give the same u-coordinate (`toU_ladderXZ_eq`).
3. The fork's `x25519` runs 255 bits. For a scalar below `2 ^ 255`, 256 bits give the same
   result (`ladderXZ_256_eq_255`), by EllipticCurve's `MontgomeryModel.ladder_eq_xMul`.

Both sides compute in `ZMod (2 ^ 255 - 19)`. The fork names the prime `curve25519.p`, and
`transport` moves its ladder to `ZMod (2 ^ 255 - 19)` with `curve25519.p_def`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open ForkSim.LadderMath
open MontgomeryModel (XZ)

namespace ForkSim

/-- The reference prime is the fork's prime, so `ZMod (2 ^ 255 - 19)` is a field. -/
instance : Fact (Nat.Prime _root_.field.p) :=
  ⟨by rw [show _root_.field.p = curve25519.p from curve25519.p_def.symm]; exact curve25519.p_prime⟩

/-! ## Bytes -/

/-- The reference reads bytes with `foldr` over the indices. This is `Nat.ofDigits 256`. -/
theorem foldr_range_eq_ofDigits (l : List ℕ) :
    (List.range l.length).foldr (fun i acc => acc * 256 + l[i]!) 0 = Nat.ofDigits 256 l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, ih, Nat.ofDigits_cons]
    ring

/-- Index `i` of the list of byte values is the value of byte `i`. -/
theorem map_val_getElem! (b : Array U8 32#usize) (i : ℕ) :
    (b.val.map (fun x => x.val))[i]! = (b.val[i]!).val := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  cases b.val[i]? <;> rfl

/-- `fe_from_bytes` reads the bytes as `asNat 8`, reduced mod p. -/
theorem fe_from_bytes_eq (b : Array U8 32#usize) :
    _root_.field.fe_from_bytes b =
      ok (show _root_.field.Fe from ((b.asNat 8 : ℕ) : ZMod _root_.field.p)) := by
  unfold _root_.field.fe_from_bytes
  have hlen : (b.val.map (fun x => x.val)).length = 32 := by simp
  have h := foldr_range_eq_ofDigits (b.val.map (fun x => x.val))
  rw [hlen] at h
  simp only [map_val_getElem!] at h
  rw [h, Array.asNat_def]
  rfl

/-- `fe_to_bytes` returns bytes whose value is the canonical representative. -/
theorem fe_to_bytes_val (a : _root_.field.Fe) (r : Array U8 32#usize)
    (h : _root_.field.fe_to_bytes a = ok r) :
    r.asNat 8 = ZMod.val (show ZMod _root_.field.p from a) := by
  unfold _root_.field.fe_to_bytes at h
  simp only [ok.injEq] at h
  subst h
  have hn : ZMod.val (a : ZMod _root_.field.p) < 256 ^ 32 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by simp)
  show _ = ZMod.val (a : ZMod _root_.field.p)
  rw [Array.asNat_eq_sum, show (32#usize).val = 32 from rfl]
  conv_rhs => rw [← Nat.mod_eq_of_lt hn, ← Nat.sum_digits_eq_mod 256 32]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < 32 := by simpa using hi
  rw [Array.getElem!_Nat_eq, Array.from_val]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, hi, _root_.dite_true, Option.getD_some,
    UScalar.ofNatCore_val_eq, pow_mul]
  norm_num

/-! ## Clamping -/

/-- The reference `mask_scalar` and the fork's `clamp_integer` have the same Lean body. -/
theorem mask_scalar_eq (s : Array U8 32#usize) :
    x25519_ref.mask_scalar s = Curve25519Dalek.scalar.clamp_integer s := rfl

/-- `mask_scalar s` returns the bytes of the fork's `clamp`. -/
theorem mask_scalar_asNat (s : Array U8 32#usize) :
    x25519_ref.mask_scalar s ⦃ m => m.asNat 8 = curve25519.clamp (s.asNat 8) ⦄ := by
  rw [mask_scalar_eq]
  apply spec_mono (Curve25519Dalek.scalar.clamp_integer_spec s)
  intro m hm
  have := curve25519.clamp_add_mod_eight (s.asNat 8)
  omega

/-- The reference bit `kbit k j` is bit `j` of `k.asNat 8`. -/
theorem kbit_eq_testBit (k : Array U8 32#usize) (j : ℕ) :
    kbit k j = (k.asNat 8).testBit j := by
  have hd : ∀ i < (32#usize).val, k[i]!.val < 2 ^ 8 := fun i _ => by
    have := (k[i]!).hBounds; simpa using this
  have hbyte := Array.asNat_div_pow_mod 8 k hd (j / 8)
  have e1 : (k.asNat 8).testBit j = (k[j / 8]!.val).testBit (j % 8) := by
    rw [← hbyte, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
      show j % 8 + 8 * (j / 8) = j by omega]
    simp [show j % 8 < 8 by omega]
  rw [e1, Array.getElem!_Nat_eq]
  unfold kbit Nat.testBit
  generalize (k.val[j / 8]!).val >>> (j % 8) = x
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · simp [Nat.one_and_eq_mod_two, h]
  · simp [Nat.one_and_eq_mod_two, h]

/-! ## The fork's ladder state -/

section Ladder
variable {K : Type*} [Field K]

/-- The state of the fork's ladder with the pending swap applied: the reference state. -/
def toPair (s : XZ.LadderState K) : Pt K × Pt K :=
  cswap s.swap ((s.R₀.U, s.R₀.W), (s.R₁.U, s.R₁.W))

/-- One step of the fork's ladder is one reference step `lstep`. -/
theorem toPair_ladderStep (x1 : K) (s : XZ.LadderState K) (b : Bool) :
    toPair (XZ.ladderStep 121665 x1 s b) = lstep x1 b (toPair s) := by
  obtain ⟨⟨U0, W0⟩, ⟨U1, W1⟩, sw⟩ := s
  cases sw <;> cases b <;>
    simp only [toPair, XZ.ladderStep, XZ.cswap, XZ.dbl, XZ.add, lstep, cswap, pad, dbl, dadd,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true] <;>
    exact Prod.ext (Prod.ext (by ring) (by ring)) (Prod.ext (by ring) (by ring))

/-- The fork's ladder loop over bits `t - 1, …, 0` of `k` is the reference ladder over the
same bits. -/
theorem toPair_ladderLoop (x1 : K) (k : ℕ) :
    ∀ (t : ℕ) (s : XZ.LadderState K), toPair (XZ.ladderLoop 121665 x1 k t s) =
      ladder x1 ((List.range t).reverse.map k.testBit) (toPair s) := by
  intro t s
  rw [XZ.ladderLoop_eq_foldl, ladder]
  exact (List.foldl_hom toPair fun s b => (toPair_ladderStep x1 s b).symm).symm

/-- `(U, W)` of the fork's projective ladder over bits `bits - 1, …, 0` of `k` is the first point
of the reference ladder over the same bits, from `((1, 0), (u, 1))`. -/
theorem ladderXZ_eq (bits k : ℕ) (u : K) :
    ((XZ.ladderXZ (121665 : K) bits k u).U, (XZ.ladderXZ (121665 : K) bits k u).W) =
      (ladder u ((List.range bits).reverse.map k.testBit) ((1, 0), (u, 1))).1 := by
  have h0 : (((1 : K), (0 : K)), (u, (1 : K))) = toPair ⟨⟨1, 0⟩, ⟨u, 1⟩, false⟩ := rfl
  rw [h0, ← toPair_ladderLoop]
  unfold XZ.ladderXZ toPair
  generalize XZ.ladderLoop 121665 u k bits ⟨⟨1, 0⟩, ⟨u, 1⟩, false⟩ = s
  obtain ⟨⟨U0, W0⟩, ⟨U1, W1⟩, sw⟩ := s
  cases sw <;> rfl

end Ladder

/-- Over a field `K`, `toU` of the fork's projective ladder over bits `bits - 1, …, 0` of `k`
is `enc` of the first point of the reference ladder over the same bits. -/
theorem toU_ladderXZ_eq {K : Type*} [Field K] (bits k : ℕ) (u : K) :
    (XZ.ladderXZ (121665 : K) bits k u).toU =
      enc (ladder u ((List.range bits).reverse.map k.testBit) ((1, 0), (u, 1))).1 := by
  rw [← ladderXZ_eq]
  simp only [XZ.toU, enc, div_eq_mul_inv]

/-! ## The prime -/

/-- For a prime `q = 2 ^ 255 - 19`, the 255-bit fork ladder has the same `val` in `ZMod q` as in
`ZMod field.p`. `x25519_eq` uses it with `q = curve25519.p`. -/
theorem transport (c n : ℕ) : ∀ (q : ℕ) [Fact q.Prime], q = 2 ^ 255 - 19 →
    ((XZ.ladderXZ (121665 : ZMod q) 255 c ((n % 2 ^ 255 : ℕ) : ZMod q)).toU).val =
      ((XZ.ladderXZ (121665 : ZMod _root_.field.p) 255 c
        ((n % 2 ^ 255 : ℕ) : ZMod _root_.field.p)).toU).val := by
  intro q _ hq
  subst hq
  rfl

/-- For `c < 2 ^ 255`, the ladder of `curve25519.montgomery` over 256 bits of `c` and over 255
bits of `c` give the same u-coordinate. Both are `xMul 2 c u` (`ladder_eq_xMul`). -/
theorem ladderXZ_256_eq_255_curve (c : ℕ) (hc : c < 2 ^ 255) (u : ZMod curve25519.p) :
    (XZ.ladderXZ (121665 : ZMod curve25519.p) 256 c u).toU =
      (XZ.ladderXZ (121665 : ZMod curve25519.p) 255 c u).toU := by
  have h := MontgomeryModel.ladder_eq_xMul (M := curve25519.montgomery)
    curve25519.not_isSquare_two (bits := 256) (k := c) (by omega) u
  rw [← MontgomeryModel.ladder_eq_xMul (M := curve25519.montgomery)
    curve25519.not_isSquare_two hc u] at h
  simpa only [MontgomeryModel.ladder, XZ.ladder, curve25519.montgomery_a24_eq] using h

/-- `ladderXZ_256_eq_255_curve` in `ZMod field.p`: for `c < 2 ^ 255`, the extra reference
iteration at bit 255 does not change the u-coordinate. -/
theorem ladderXZ_256_eq_255 (c : ℕ) (hc : c < 2 ^ 255) (u : ZMod _root_.field.p) :
    (XZ.ladderXZ (121665 : ZMod _root_.field.p) 256 c u).toU =
      (XZ.ladderXZ (121665 : ZMod _root_.field.p) 255 c u).toU := by
  have key : ∀ (q : ℕ) [Fact q.Prime], q = curve25519.p → ∀ u : ZMod q,
      (XZ.ladderXZ (121665 : ZMod q) 256 c u).toU = (XZ.ladderXZ 121665 255 c u).toU := by
    intro q _ hq
    subst hq
    exact ladderXZ_256_eq_255_curve c hc
  exact key _ curve25519.p_def.symm u

/-- The fork's `x25519` as the 256-bit ladder in `ZMod (2 ^ 255 - 19)`, the bit count of the
reference. -/
theorem x25519_eq (k n : ℕ) :
    curve25519.x25519 k n =
      ((XZ.ladderXZ (121665 : ZMod _root_.field.p) 256 (curve25519.clamp k)
        ((n % 2 ^ 255 : ℕ) : ZMod _root_.field.p)).toU).val := by
  rw [ladderXZ_256_eq_255 _ (curve25519.clamp_lt k), ← transport _ _ curve25519.p curve25519.p_def]
  simp only [curve25519.x25519, curve25519.encodeU, curve25519.decodeU, MontgomeryModel.ladder,
    XZ.ladder, curve25519.montgomery_a24_eq]

/-! ## The reference -/

/-- `decode_point u` returns `(u.asNat 8 % 2 ^ 255, 1)`: bit 255 masked. -/
theorem decode_point_spec (u : Array U8 32#usize) :
    x25519_ref.decode_point u ⦃ r =>
      r = (show _root_.field.Fe from ((u.asNat 8 % 2 ^ 255 : ℕ) : ZMod _root_.field.p), 1) ⦄ := by
  unfold x25519_ref.decode_point
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, _⟩
  step as ⟨u1, hu1⟩
  rw [fe_from_bytes_eq]
  simp only [bind_ok, fe_lit_eq, UScalar.ofNatCore_val_eq, Nat.cast_one]
  have hd : ∀ i < (32#usize).val, u[i]!.val < 2 ^ 8 := fun i _ => by
    have := (u[i]!).hBounds; simpa using this
  have hlast := Array.getElem!_last_eq_asNat_div 8 u hd (by simp)
  have hset := Array.asNat_set_add 8 u 31#usize i1 (by simp)
  have hlt := Array.asNat_lt 8 u hd
  have hx : i1.val = i.val % 128 := by
    rw [hi1, UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have hi' := congrArg UScalar.val hi
  have heq : u1.asNat 8 = u.asNat 8 % 2 ^ 255 := by
    rw [hu1]
    simp only [show (32#usize).val = 32 from rfl, show (31#usize).val = 31 from rfl] at hset hlast hlt
    norm_num at hset hlast hlt
    omega
  rw [heq]
  refine spec_bind ((spec_ok _).mpr rfl) ?_
  intro f hf
  rw [hf]
  exact (spec_ok _).mpr rfl

/-- **The reference X25519 is the fork's `x25519`.** For all 32-byte `k` and `u`,
`x25519_scalarmult k u` returns bytes whose value is `x25519 (k.asNat 8) (u.asNat 8)`. -/
theorem x25519_scalarmult_spec (k u : Array U8 32#usize) :
    x25519_ref.x25519_scalarmult k u ⦃ r =>
      r.asNat 8 = curve25519.x25519 (k.asNat 8) (u.asNat 8) ⦄ := by
  unfold x25519_ref.x25519_scalarmult x25519_ref.decode_scalar
  step with mask_scalar_asNat as ⟨m, hm⟩
  step with decode_point_spec as ⟨p_, hp⟩
  step with montgomery_ladder_eq as ⟨r, hr⟩
  rw [encode_point_eq]
  obtain ⟨b, hb⟩ : ∃ b, _root_.field.fe_to_bytes (r.1 * r.2⁻¹) = ok b := ⟨_, rfl⟩
  rw [hb, spec_ok, fe_to_bytes_val _ _ hb, x25519_eq, toU_ladderXZ_eq, hr, hp]
  -- The reference bits are the bits of `clamp`.
  have hbits : refBits m =
      (List.range 256).reverse.map (curve25519.clamp (k.asNat 8)).testBit := by
    unfold refBits bitsFrom
    exact List.map_congr_left fun j _ => by rw [kbit_eq_testBit m j, hm]
  rw [hbits]
  rfl

/-- The bytes of the basepoint `u = 9`. -/
theorem nine_asNat : ((Array.repeat 32#usize 0#u8).set 0#usize 9#u8).asNat 8 = 9 := by
  rfl

/-- **The reference public key is the fork's `x25519 k 9`.** -/
theorem x25519_secret_to_public_spec (k : Array U8 32#usize) :
    x25519_ref.x25519_secret_to_public k ⦃ r =>
      r.asNat 8 = curve25519.x25519 (k.asNat 8) 9 ⦄ := by
  unfold x25519_ref.x25519_secret_to_public
  step as ⟨base, hbase⟩
  apply spec_mono (x25519_scalarmult_spec k base)
  intro r hr
  rw [hr, hbase, nine_asNat]

end ForkSim
