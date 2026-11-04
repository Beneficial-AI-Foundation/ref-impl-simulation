import Sim.X25519
import DalekSim.Choice

/-! # The all-zero check: `was_contributory` against `x25519_is_all_zero`

RFC 7748, section 6.1, lets both parties check whether the shared secret `K` is all zero,
for example by an OR of all bytes. The hacspec spec has no such check, so the reference
port has our addition `x25519_is_all_zero` (`ref-plain/src/lib.rs`), which computes this OR.

x25519-dalek's `SharedSecret::was_contributory` is `!self.0.is_identity()`. The identity is
32 zero bytes, and `MontgomeryPoint::ct_eq` decodes both sides with `from_bytes` and compares
them mod p. So it ignores bit 255 and treats the bytes of `p` as zero. The raw check and the
mod p check agree on canonical bytes, and `x25519_scalarmult` returns canonical bytes. The
theorems state the composition: `diffie_hellman` and then `was_contributory`, against
`x25519_scalarmult` and then the negation of `x25519_is_all_zero`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace X25519Sim

open DalekSim

/-! ## The reference check -/

/-- If `a ||| b = 0`, then `a = 0` and `b = 0`. -/
theorem nat_or_eq_zero {a b : Nat} (h : a ||| b = 0) : a = 0 ∧ b = 0 := by
  constructor <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
  · have := congrArg (fun n => Nat.testBit n i) h
    simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at this
    simp [this]

/-- The loop of `x25519_is_all_zero` from index `i` returns 0 iff `acc` is 0 and the bytes
from `i` on are 0. -/
theorem is_all_zero_loop_spec (k : Array U8 32#usize) :
    ∀ (n : Nat) (acc : U8) (i : Usize), i.val + n = 32 →
      ∃ r, x25519_ref.x25519_is_all_zero_loop k acc i = ok r ∧
        (r = 0#u8 ↔ acc = 0#u8 ∧ ∀ j, i.val ≤ j → j < 32 → k.val[j]! = 0#u8)
  | 0, acc, i, h => by
    refine ⟨acc, ?_, ?_⟩
    · rw [x25519_ref.x25519_is_all_zero_loop]
      simp only [show ¬ i < 32#usize by scalar_tac, if_false]
    · constructor
      · intro hr; exact ⟨hr, fun j hj hj' => by omega⟩
      · exact fun h => h.1
  | n + 1, acc, i, h => by
    have hi : i.val < 32 := by omega
    obtain ⟨v, hv, hv'⟩ := exists_ok_of_spec (Array.index_usize_spec k i (by scalar_tac))
    have hv'' : v = k.val[i.val]! := by rw [hv', getElem!_pos]
    obtain ⟨i2, hi2, hi2'⟩ := exists_ok_of_spec (Usize.add_spec (x := i) (y := 1#usize)
      (by scalar_tac))
    obtain ⟨r, hr, hiff⟩ := is_all_zero_loop_spec k n (acc ||| v) i2 (by simp at hi2'; omega)
    refine ⟨r, ?_, ?_⟩
    · rw [x25519_ref.x25519_is_all_zero_loop]
      simp only [show i < 32#usize by scalar_tac, if_true]
      rw [hv]
      simp only [lift, bind_ok, hi2]
      exact hr
    · rw [hiff]
      have hi2v : i2.val = i.val + 1 := by simp at hi2'; omega
      rw [hi2v]
      constructor
      · rintro ⟨hor, hrest⟩
        have hor' := congrArg UScalar.val hor
        rw [UScalar.val_or] at hor'
        obtain ⟨ha, hb⟩ := nat_or_eq_zero hor'
        refine ⟨UScalar.eq_of_val_eq ha, fun j hj hj' => ?_⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · rw [← hv'']; exact UScalar.eq_of_val_eq hb
        · exact hrest j (by omega) hj'
      · rintro ⟨hacc, hall⟩
        refine ⟨?_, fun j hj hj' => hall j (by omega) hj'⟩
        rw [hacc, hv'', hall i.val le_rfl hi]
        rfl

/-- `x25519_is_all_zero k` returns `true` iff `k` reads as 0. -/
theorem is_all_zero_eq (k : Array U8 32#usize) :
    x25519_ref.x25519_is_all_zero k = ok (decide (U8x32_as_Nat k = 0)) := by
  obtain ⟨r, hr, hiff⟩ := is_all_zero_loop_spec k 32 0#u8 0#usize (by simp)
  unfold x25519_ref.x25519_is_all_zero
  rw [hr, bind_ok, ok.injEq, decide_eq_decide, hiff, U8x32_eq_zero_iff]
  simp

/-! ## The real check -/

/-- The field `ct_eq` returns 1 iff `toZ a = toZ b`. -/
theorem fe_ct_eq_z (a b : FE) :
    backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq.ct_eq a b
      ⦃ c => (c.val = 1#u8 ↔ toZ a = toZ b) ⦄ := by
  apply spec_mono (fe_ct_eq_mod a b)
  intro c hc
  rw [hc]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).symm

/-- `MontgomeryPoint::ct_eq` returns 1 iff the two u-coordinates decode to the same element of
`ZMod p`. -/
theorem montgomery_ct_eq_spec (x y : Array U8 32#usize) :
    x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq
      x y ⦃ c => (c.val = 1#u8 ↔ decodeU x = decodeU y) ⦄ := by
  unfold x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq
  step with from_bytes_z as ⟨fx, hfx, _⟩
  step with from_bytes_z as ⟨fy, hfy, _⟩
  apply spec_mono (fe_ct_eq_z fx fy)
  intro c hc
  rw [hc, hfx, hfy]

/-- `was_contributory` returns `true` iff the bytes do not decode to 0 in `ZMod p`. -/
theorem was_contributory_spec (x : Array U8 32#usize) :
    x25519_dalek.x25519.SharedSecret.was_contributory x ⦃ b => (b = true ↔ decodeU x ≠ 0) ⦄ := by
  unfold x25519_dalek.x25519.SharedSecret.was_contributory
    x25519_dalek.curve25519_dalek.traits.IsIdentity.Blanket.is_identity
  simp only [x25519_dalek.curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity,
    bind_ok]
  step with montgomery_ct_eq_spec as ⟨c, hc⟩
  have hz : decodeU (Array.repeat 32#usize 0#u8) = 0 := by
    rw [decodeU, U8x32_zero]; rfl
  simp only [Bool.Insts.CoreConvertFromChoice.from, bind_ok, spec_ok]
  rw [hz] at hc
  rcases c.valid with h | h <;> rw [h] at hc ⊢ <;> simp_all

/-! ## Canonical output -/

/-- `x25519_scalarmult` returns canonical bytes: they read as a number below `p`. -/
theorem x25519_scalarmult_canonical (s u r : Array U8 32#usize)
    (h : x25519_ref.x25519_scalarmult s u = ok r) : U8x32_as_Nat r < p := by
  obtain ⟨k, hk, _⟩ := exists_ok_of_spec (mask_scalar_spec s)
  unfold x25519_ref.x25519_scalarmult x25519_ref.decode_scalar at h
  rw [hk, bind_ok, eq_ok_of_spec (decode_point_spec u), bind_ok,
    eq_ok_of_spec (montgomery_ladder_eq k (decodeU u, 1)), bind_ok, encode_point_eq] at h
  rw [fe_to_bytes_val _ r h]
  exact ZMod.val_lt _

/-- On canonical bytes, decoding to 0 is reading as 0. -/
theorem decodeU_eq_zero_iff (r : Array U8 32#usize) (h : U8x32_as_Nat r < p) :
    decodeU r = 0 ↔ U8x32_as_Nat r = 0 := by
  have h255 : U8x32_as_Nat r % 2 ^ 255 = U8x32_as_Nat r :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le h (by simp [p]))
  change ((U8x32_as_Nat r % 2 ^ 255 : ℕ) : ZMod _root_.field.p) = 0 ↔ _
  rw [h255, ZMod.natCast_eq_zero_iff]
  constructor
  · intro hd; exact Nat.eq_zero_of_dvd_of_lt hd h
  · intro h0; rw [h0]; exact dvd_zero _

/-! ## The composition theorems -/

/-- If `x25519_scalarmult s u = ok r`, then `was_contributory r` returns
`!x25519_is_all_zero r`. -/
theorem was_contributory_refines (s u r : Array U8 32#usize)
    (hr : x25519_ref.x25519_scalarmult s u = ok r) :
    x25519_dalek.x25519.SharedSecret.was_contributory r ⦃ b =>
      (do
        let k ← x25519_ref.x25519_scalarmult s u
        let z ← x25519_ref.x25519_is_all_zero k
        ok (!z)) = ok b ⦄ := by
  apply spec_mono (was_contributory_spec r)
  intro b hb
  have hz := decodeU_eq_zero_iff r (x25519_scalarmult_canonical s u r hr)
  rw [hr, bind_ok, is_all_zero_eq, bind_ok, ok.injEq]
  cases b <;> simp_all

/-- `StaticSecret.diffie_hellman s u` followed by `SharedSecret.was_contributory` returns
`!x25519_is_all_zero (x25519_scalarmult s u)`. -/
theorem static_diffie_hellman_was_contributory_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.StaticSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let k ← x25519_ref.x25519_scalarmult s u
        let z ← x25519_ref.x25519_is_all_zero k
        ok (!z)) = ok b ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (static_diffie_hellman_refines s u)
  rw [hr, bind_ok]
  exact was_contributory_refines s u r hspec

/-- As `static_diffie_hellman_was_contributory_refines`, for `EphemeralSecret`. -/
theorem ephemeral_diffie_hellman_was_contributory_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.EphemeralSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let k ← x25519_ref.x25519_scalarmult s u
        let z ← x25519_ref.x25519_is_all_zero k
        ok (!z)) = ok b ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (ephemeral_diffie_hellman_refines s u)
  rw [hr, bind_ok]
  exact was_contributory_refines s u r hspec

/-- As `static_diffie_hellman_was_contributory_refines`, for `ReusableSecret`. -/
theorem reusable_diffie_hellman_was_contributory_refines (s u : Array U8 32#usize) :
    (do
      let ss ← x25519_dalek.x25519.ReusableSecret.diffie_hellman s u
      x25519_dalek.x25519.SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let k ← x25519_ref.x25519_scalarmult s u
        let z ← x25519_ref.x25519_is_all_zero k
        ok (!z)) = ok b ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (reusable_diffie_hellman_refines s u)
  rw [hr, bind_ok]
  exact was_contributory_refines s u r hspec

end X25519Sim
