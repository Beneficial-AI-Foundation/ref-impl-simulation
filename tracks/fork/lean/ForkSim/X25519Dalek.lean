import ForkSim.Montgomery
import X25519Dalek.Funs
import Proofs.Edwards.MulBaseClamped
import Proofs.Edwards.ToMontgomery
import Proofs.Traits.IsIdentity
import Proofs.Montgomery.Eq
import Zeroize.Instances

/-! # x25519-dalek 3.0.0 against the translated reference

x25519-dalek calls curve25519-dalek for all curve arithmetic. Its Lean translation
(`X25519Dalek/Funs.lean`) calls the fork's translation of curve25519-dalek 5.0.0 through
`X25519Dalek/FunsExternal.lean`. This file states each function that x25519-dalek 3.0.0
defines or derives in its module `x25519`, with the features of section 8.2 of the track
README, except the `Debug` and `Hash` impls. It does not state the default trait methods that
the impls inherit, such as `PartialEq::ne` and `Clone::clone_from`. It proves the curve
operations against the reference from `ForkSim.mul_clamped_refines` and from the fork's specs. The theorems state
return values. They do not state the ownership rules of Rust, for example that
`EphemeralSecret::diffie_hellman` consumes the secret. The Rust compiler enforces these rules. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace ForkSim

open x25519_dalek.x25519

/-- If `m` returns bytes with the little-endian value `n`, and `r` has the value `n`, then
`m = ok r`. -/
theorem refines_of_asNat {r : Array U8 32#usize} {m : Result (Array U8 32#usize)} {n : ℕ}
    (hm : m ⦃ r' => r'.asNat 8 = n ⦄) (hr : r.asNat 8 = n) : m = ok r := by
  obtain ⟨r', hr', hval⟩ := exists_ok_of_spec hm
  rw [hr', Array.eq_of_asNat_eq (hval.trans hr.symm)]

/-! ## Shared secret -/

/-- **`StaticSecret::diffie_hellman` refines the reference.** For all 32-byte `k` and `u`,
`diffie_hellman k u` returns the bytes of `x25519_scalarmult k u`. -/
theorem static_diffie_hellman_refines (k u : Array U8 32#usize) :
    StaticSecret.diffie_hellman k u ⦃ r => x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  unfold StaticSecret.diffie_hellman
  simpa using mul_clamped_refines u k

/-- **`ReusableSecret::diffie_hellman` refines the reference.** -/
theorem reusable_diffie_hellman_refines (k u : Array U8 32#usize) :
    ReusableSecret.diffie_hellman k u ⦃ r => x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  unfold ReusableSecret.diffie_hellman
  simpa using mul_clamped_refines u k

/-- **`EphemeralSecret::diffie_hellman` refines the reference.** -/
theorem ephemeral_diffie_hellman_refines (k u : Array U8 32#usize) :
    EphemeralSecret.diffie_hellman k u ⦃ r => x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  unfold EphemeralSecret.diffie_hellman
  simpa using mul_clamped_refines u k

/-! ## Public key -/

/-- `EdwardsPoint::mul_base_clamped` and then `to_montgomery` returns the bytes of
`x25519_secret_to_public k`, in each of the four builds. -/
theorem mul_base_clamped_to_montgomery_refines (k : Array U8 32#usize) :
    (do
      let ep ← curve25519_dalek.edwards.EdwardsPoint.mul_base_clamped k
      curve25519_dalek.edwards.EdwardsPoint.to_montgomery ep) ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  have hfin : ∀ r : Array U8 32#usize,
      r.asNat 8 = curve25519.encodeU (curve25519.edwardsToMontgomery
        (curve25519.clamp (k.asNat 8) • curve25519.basepoint)).u →
      x25519_ref.x25519_secret_to_public k = ok r := fun r hr =>
    refines_of_asNat (x25519_secret_to_public_spec k)
      (hr.trans (curve25519.x25519_basepoint_edwards _).symm)
  unfold curve25519_dalek.edwards.EdwardsPoint.mul_base_clamped
  simp only [get_target, bind_ok]
  split_ifs
  · obtain ⟨p, hp, hon, hpt, hlt⟩ := exists_ok_of_spec
      (Curve25519Dalek.edwards.«EdwardsPointx86_64-tables».mul_base_clamped_spec k)
    rw [hp, bind_ok, bind_ok, curve25519_dalek.edwards.EdwardsPoint.to_montgomery]
    refine spec_mono (Curve25519Dalek.edwards.«EdwardsPointx86_64-tables».to_montgomery_spec_point
      p hlt hon) fun r hr => hfin r ?_
    rw [← Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def, hr, hpt]
  · obtain ⟨p, hp, hon, hpt, hlt⟩ := exists_ok_of_spec
      (Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables».mul_base_clamped_spec k)
    rw [hp, bind_ok, bind_ok, curve25519_dalek.edwards.EdwardsPoint.to_montgomery]
    refine spec_mono
      (Curve25519Dalek.edwards.«EdwardsPointx86_64-no-tables».to_montgomery_spec_point
        p hlt hon) fun r hr => hfin r ?_
    rw [← Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def, hr, hpt]
  · obtain ⟨p, hp, hon, hpt, hlt⟩ := exists_ok_of_spec
      (Curve25519Dalek.edwards.«EdwardsPointi686-tables».mul_base_clamped_spec k)
    rw [hp, bind_ok, bind_ok, curve25519_dalek.edwards.EdwardsPoint.to_montgomery]
    refine spec_mono (Curve25519Dalek.edwards.«EdwardsPointi686-tables».to_montgomery_spec_point
      p hlt hon) fun r hr => hfin r ?_
    rw [← Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def, hr, hpt]
  · obtain ⟨p, hp, hon, hpt, hlt⟩ := exists_ok_of_spec
      (Curve25519Dalek.edwards.«EdwardsPointi686-no-tables».mul_base_clamped_spec k)
    rw [hp, bind_ok, bind_ok, curve25519_dalek.edwards.EdwardsPoint.to_montgomery]
    refine spec_mono
      (Curve25519Dalek.edwards.«EdwardsPointi686-no-tables».to_montgomery_spec_point
        p hlt hon) fun r hr => hfin r ?_
    rw [← Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def, hr, hpt]

/-- **`PublicKey::from(&StaticSecret)` refines the reference.** For every 32-byte `k`, it returns
the bytes of `x25519_secret_to_public k`. -/
theorem public_key_from_static_refines (k : Array U8 32#usize) :
    PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from k ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  unfold PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from
  simpa using mul_base_clamped_to_montgomery_refines k

/-- **`PublicKey::from(&EphemeralSecret)` refines the reference.** -/
theorem public_key_from_ephemeral_refines (k : Array U8 32#usize) :
    PublicKey.Insts.CoreConvertFromSharedAEphemeralSecret.from k ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  unfold PublicKey.Insts.CoreConvertFromSharedAEphemeralSecret.from
  simpa using mul_base_clamped_to_montgomery_refines k

/-- **`PublicKey::from(&ReusableSecret)` refines the reference.** -/
theorem public_key_from_reusable_refines (k : Array U8 32#usize) :
    PublicKey.Insts.CoreConvertFromSharedAReusableSecret.from k ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  unfold PublicKey.Insts.CoreConvertFromSharedAReusableSecret.from
  simpa using mul_base_clamped_to_montgomery_refines k

/-! ## The bare function, the base point and the accessors -/

/-- **`x25519` refines the reference.** For all 32-byte `k` and `u`, `x25519 k u` returns the
bytes of `x25519_scalarmult k u`. -/
theorem x25519_refines (k u : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k u ⦃ r => x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  unfold x25519_dalek.x25519.x25519
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (mul_clamped_refines u k)
  simp only [curve25519_dalek.montgomery.MontgomeryPoint.mul_clamped] at hr ⊢
  rw [hr, bind_ok]
  exact spec_mono (Curve25519Dalek.montgomery.MontgomeryPoint.to_bytes_spec r)
    fun r' h => h ▸ hspec

/-- `X25519_BASEPOINT_BYTES` is the array with 9 at index 0 and 0 at the other 31 indices.
`x25519_secret_to_public` builds the same array. -/
theorem basepoint_eq :
    Array.update (Array.repeat 32#usize 0#u8) 0#usize 9#u8 =
      ok x25519_dalek.x25519.X25519_BASEPOINT_BYTES := by
  unfold x25519_dalek.x25519.X25519_BASEPOINT_BYTES
  rfl

/-- **`x25519` on `X25519_BASEPOINT_BYTES` refines `x25519_secret_to_public`.** -/
theorem x25519_basepoint_refines (k : Array U8 32#usize) :
    x25519_dalek.x25519.x25519 k x25519_dalek.x25519.X25519_BASEPOINT_BYTES ⦃ r =>
      x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  unfold x25519_ref.x25519_secret_to_public
  simp only [basepoint_eq, bind_ok]
  exact x25519_refines k _

/-- The accessors and the two `From<[u8; 32]>` impls return the 32 bytes that they wrap. -/
theorem static_secret_to_bytes_eq (s : Array U8 32#usize) : StaticSecret.to_bytes s = ok s := rfl
theorem static_secret_as_bytes_eq (s : Array U8 32#usize) : StaticSecret.as_bytes s = ok s := rfl
theorem public_key_to_bytes_eq (p : Array U8 32#usize) : PublicKey.to_bytes p = ok p := rfl
theorem public_key_as_bytes_eq (p : Array U8 32#usize) : PublicKey.as_bytes p = ok p := rfl
theorem shared_secret_to_bytes_eq (s : Array U8 32#usize) : SharedSecret.to_bytes s = ok s := rfl
theorem shared_secret_as_bytes_eq (s : Array U8 32#usize) : SharedSecret.as_bytes s = ok s := rfl
theorem static_secret_from_eq (b : Array U8 32#usize) :
    StaticSecret.Insts.CoreConvertFromArrayU832.from b = ok b := rfl
theorem public_key_from_bytes_eq (b : Array U8 32#usize) :
    PublicKey.Insts.CoreConvertFromArrayU832.from b = ok b := rfl

/-- **The x25519-dalek calls of libsignal's `PrivateKey::calculate_agreement` refine the
reference.** libsignal `fc90b90f` computes
`*self.secret.diffie_hellman(&PublicKey::from(*their_public_key)).as_bytes()`. -/
theorem static_diffie_hellman_as_bytes_refines (k u : Array U8 32#usize) :
    (do
      let pk ← PublicKey.Insts.CoreConvertFromArrayU832.from u
      let ss ← StaticSecret.diffie_hellman k pk
      SharedSecret.as_bytes ss) ⦃ r => x25519_ref.x25519_scalarmult k u = ok r ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (static_diffie_hellman_refines k u)
  rw [public_key_from_bytes_eq, bind_ok, hr, bind_ok, shared_secret_as_bytes_eq]
  exact (spec_ok _).mpr hspec

/-- **The x25519-dalek calls of libsignal's `PrivateKey::derive_public_key_bytes` refine the
reference.** libsignal `fc90b90f` computes `*PublicKey::from(&self.secret).as_bytes()`. -/
theorem public_key_from_static_as_bytes_refines (k : Array U8 32#usize) :
    (do
      let pk ← PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from k
      PublicKey.as_bytes pk) ⦃ r => x25519_ref.x25519_secret_to_public k = ok r ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (public_key_from_static_refines k)
  rw [hr, bind_ok, public_key_as_bytes_eq]
  exact (spec_ok _).mpr hspec

/-! ## The other trait impls

`Clone`, `AsRef<[u8]>`, `PartialEq` of `PublicKey`, and `Zeroize for PublicKey`. The `Copy` and
`Eq` impls are markers without functions. -/

/-- `Clone` of `PublicKey`, `StaticSecret` and `ReusableSecret` returns the same bytes. -/
theorem public_key_clone_eq (p : Array U8 32#usize) :
    PublicKey.Insts.CoreCloneClone.clone p = ok p := rfl

theorem static_secret_clone_eq (s : Array U8 32#usize) :
    StaticSecret.Insts.CoreCloneClone.clone s = ok s := by
  obtain ⟨a, ha, hs⟩ := exists_ok_of_spec
    (core.array.CloneArray.clone_spec core.clone.CloneU8 s (fun _ _ => rfl))
  rw [StaticSecret.Insts.CoreCloneClone.clone, ha, bind_ok, hs]

theorem reusable_secret_clone_eq (s : Array U8 32#usize) :
    ReusableSecret.Insts.CoreCloneClone.clone s = ok s := by
  obtain ⟨a, ha, hs⟩ := exists_ok_of_spec
    (core.array.CloneArray.clone_spec core.clone.CloneU8 s (fun _ _ => rfl))
  rw [ReusableSecret.Insts.CoreCloneClone.clone, ha, bind_ok, hs]

/-- `AsRef<[u8]>` of `PublicKey`, `StaticSecret` and `SharedSecret` returns a slice of the 32
bytes. -/
theorem public_key_as_ref_eq (p : Array U8 32#usize) :
    PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref p = ok p.to_slice := by
  rw [PublicKey.Insts.CoreConvertAsRefSliceU8.as_ref, public_key_as_bytes_eq, bind_ok]

theorem static_secret_as_ref_eq (s : Array U8 32#usize) :
    StaticSecret.Insts.CoreConvertAsRefSliceU8.as_ref s = ok s.to_slice := by
  rw [StaticSecret.Insts.CoreConvertAsRefSliceU8.as_ref, static_secret_as_bytes_eq, bind_ok]

theorem shared_secret_as_ref_eq (s : Array U8 32#usize) :
    SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref s = ok s.to_slice := by
  rw [SharedSecret.Insts.CoreConvertAsRefSliceU8.as_ref, shared_secret_as_bytes_eq, bind_ok]

/-- **`PartialEq for PublicKey`** returns `true` iff the two keys decode to the same
u-coordinate. `decodeU` clears bit 255 and reduces mod `p`. So two different byte arrays can be
equal keys, for example the encodings of `u` and `u + p` for `u < 19`. -/
theorem public_key_eq_spec (a b : Array U8 32#usize) :
    PublicKey.Insts.CoreCmpPartialEqPublicKey.eq a b ⦃ r =>
      (r = true ↔ curve25519.decodeU (a.asNat 8) = curve25519.decodeU (b.asNat 8)) ⦄ := by
  unfold PublicKey.Insts.CoreCmpPartialEqPublicKey.eq
  refine spec_mono
    (Curve25519Dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.eq_spec a b)
    fun r hr => ?_
  rw [hr, Curve25519Dalek.montgomery.MontgomeryPoint.u_def,
    Curve25519Dalek.montgomery.MontgomeryPoint.u_def,
    Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def,
    Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def]

/-! ## Key generation

In Rust, `random_from_rng(&mut R) -> Self` of each secret type calls `fill_bytes` of the
generic `rand_core` RNG `R` on 32 zero bytes. It returns the written bytes as the secret,
without clamping. `diffie_hellman` and `PublicKey::from` clamp the scalar. Aeneas models the
`&mut` arguments as values that the call returns. So the translated `fill_bytes` returns the
new RNG and the new slice, and the translated `random_from_rng` returns the secret and the new
RNG.

The theorems are conditional on two hypotheses about `fill_bytes`, for every implementation of
`rand_core::CryptoRng`:
- `hfill`: `fill_bytes` returns. `rand_core` lets an implementation panic.
- `hlen`: the slice keeps its length 32. In Rust, `&mut [u8]` cannot change its length, but
  the Lean model of the trait does not state this.

The theorems do not state that the bytes are random. -/

/-- If `fill_bytes` returns the new RNG `rng'` and the bytes `s` of length 32,
**`EphemeralSecret::random_from_rng`** returns the secret `s`, and the new RNG is `rng'`. -/
theorem ephemeral_random_from_rng_spec {R E : Type} (inst : x25519_dalek.rand_core.CryptoRng R E)
    (rng rng' : R) (s : Slice U8)
    (hfill : inst.RngInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice = ok (rng', s))
    (hlen : s.length = 32) :
    EphemeralSecret.random_from_rng inst rng ⦃ p => p.1.val = s.val ∧ p.2 = rng' ⦄ := by
  unfold EphemeralSecret.random_from_rng
  step as ⟨s0, back, hs0, hback⟩
  subst hback
  rw [show s0 = (Array.repeat 32#usize 0#u8).to_slice from Slice.ext _ _ (by rw [hs0]; rfl),
    hfill, bind_ok]
  exact (spec_ok _).mpr ⟨Array.from_slice_val _ _ hlen, rfl⟩

/-- As `ephemeral_random_from_rng_spec`, for `ReusableSecret`. -/
theorem reusable_random_from_rng_spec {R E : Type} (inst : x25519_dalek.rand_core.CryptoRng R E)
    (rng rng' : R) (s : Slice U8)
    (hfill : inst.RngInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice = ok (rng', s))
    (hlen : s.length = 32) :
    ReusableSecret.random_from_rng inst rng ⦃ p => p.1.val = s.val ∧ p.2 = rng' ⦄ := by
  unfold ReusableSecret.random_from_rng
  step as ⟨s0, back, hs0, hback⟩
  subst hback
  rw [show s0 = (Array.repeat 32#usize 0#u8).to_slice from Slice.ext _ _ (by rw [hs0]; rfl),
    hfill, bind_ok]
  exact (spec_ok _).mpr ⟨Array.from_slice_val _ _ hlen, rfl⟩

/-- As `ephemeral_random_from_rng_spec`, for `StaticSecret`. -/
theorem static_random_from_rng_spec {R E : Type} (inst : x25519_dalek.rand_core.CryptoRng R E)
    (rng rng' : R) (s : Slice U8)
    (hfill : inst.RngInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice = ok (rng', s))
    (hlen : s.length = 32) :
    StaticSecret.random_from_rng inst rng ⦃ p => p.1.val = s.val ∧ p.2 = rng' ⦄ := by
  unfold StaticSecret.random_from_rng
  step as ⟨s0, back, hs0, hback⟩
  subst hback
  rw [show s0 = (Array.repeat 32#usize 0#u8).to_slice from Slice.ext _ _ (by rw [hs0]; rfl),
    hfill, bind_ok]
  exact (spec_ok _).mpr ⟨Array.from_slice_val _ _ hlen, rfl⟩

/-! ## The all-zero check: `was_contributory` against `x25519_is_all_zero`

RFC 7748, section 6.1, lets both parties check whether the shared secret is all zero, for
example by an OR of all bytes. The reference port has our addition `x25519_is_all_zero`
(`tracks/x25519/ref-plain/src/lib.rs`), which computes this OR. x25519-dalek's
`SharedSecret::was_contributory` is `!self.0.is_identity()`: it compares the u-coordinate mod p
with 0. The two checks agree on bytes below `p`, and `x25519_scalarmult` returns such bytes. -/

/-- 32 bytes read as 0 iff each byte is 0. -/
theorem asNat_eq_zero_iff (k : Array U8 32#usize) :
    k.asNat 8 = 0 ↔ ∀ j, j < 32 → k.val[j]! = 0#u8 := by
  rw [Array.asNat_eq_sum, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_range, show (32#usize).val = 32 from rfl, Array.getElem!_Nat_eq,
    mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, false_or]
  exact forall₂_congr fun j _ =>
    ⟨fun h => UScalar.eq_of_val_eq (by rw [h]; rfl), fun h => by rw [h]; rfl⟩

/-- The loop of `x25519_is_all_zero` from index `i` returns 0 iff `acc` is 0 and the bytes
from `i` on are 0. -/
theorem is_all_zero_loop_spec (k : Array U8 32#usize) :
    ∀ (n : ℕ) (acc : U8) (i : Usize), i.val + n = 32 →
      ∃ r, x25519_ref.x25519_is_all_zero_loop k acc i = ok r ∧
        (r = 0#u8 ↔ acc = 0#u8 ∧ ∀ j, i.val ≤ j → j < 32 → k.val[j]! = 0#u8)
  | 0, acc, i, h => by
    refine ⟨acc, ?_, ?_⟩
    · rw [x25519_ref.x25519_is_all_zero_loop]
      simp only [show ¬ i < 32#usize by scalar_tac, ite_false]
    · exact ⟨fun hr => ⟨hr, fun j hj hj' => by omega⟩, fun h => h.1⟩
  | n + 1, acc, i, h => by
    have hi : i.val < 32 := by omega
    obtain ⟨v, hv, hv'⟩ := exists_ok_of_spec (Array.index_usize_spec k i (by scalar_tac))
    have hv'' : v = k.val[i.val]! := by rw [hv', getElem!_pos]
    obtain ⟨i2, hi2, hi2'⟩ := exists_ok_of_spec (Usize.add_spec (x := i) (y := 1#usize)
      (by scalar_tac))
    obtain ⟨r, hr, hiff⟩ := is_all_zero_loop_spec k n (acc ||| v) i2 (by simp at hi2'; omega)
    refine ⟨r, ?_, ?_⟩
    · rw [x25519_ref.x25519_is_all_zero_loop]
      simp only [show i < 32#usize by scalar_tac, ite_true]
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
        obtain ⟨ha, hb⟩ := Nat.or_eq_zero_iff.mp hor'
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
    x25519_ref.x25519_is_all_zero k = ok (decide (k.asNat 8 = 0)) := by
  obtain ⟨r, hr, hiff⟩ := is_all_zero_loop_spec k 32 0#u8 0#usize (by simp)
  unfold x25519_ref.x25519_is_all_zero
  rw [hr, bind_ok, ok.injEq, decide_eq_decide, hiff, asNat_eq_zero_iff]
  simp

/-- `was_contributory` returns `true` iff the bytes do not decode to 0 mod p. -/
theorem was_contributory_spec (s : Array U8 32#usize) :
    SharedSecret.was_contributory s ⦃ b =>
      (b = true ↔ curve25519.decodeU (s.asNat 8) ≠ 0) ⦄ := by
  unfold SharedSecret.was_contributory
  have h := Curve25519Dalek.traits.IsIdentity.Blanket.is_identity_spec
    Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq
    Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity s
    (fun e => Curve25519Dalek.montgomery.MontgomeryPoint.asNat e = 0)
    (curve25519.decodeU (s.asNat 8) = 0)
    Curve25519Dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec
    (fun e he => spec_mono
      (Curve25519Dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq.ct_eq_spec s e)
      fun c ⟨hv, hc⟩ => ⟨hv, by
        rw [hc, Curve25519Dalek.montgomery.MontgomeryPoint.u_def,
          Curve25519Dalek.montgomery.MontgomeryPoint.u_def, he,
          Curve25519Dalek.montgomery.MontgomeryPoint.asNat_def]
        simp [curve25519.decodeU]⟩)
  obtain ⟨b, hb, hiff⟩ := exists_ok_of_spec h
  simp only [curve25519_dalek.traits.IsIdentity.Blanket.is_identity]
  rw [show Curve25519Dalek.traits.IsIdentity.Blanket.is_identity _ _ s = ok b from hb, bind_ok,
    spec_ok]
  cases b <;> simp_all

/-- Bytes below `p` decode to 0 iff they read as 0. -/
theorem decodeU_eq_zero_iff {n : ℕ} (h : n < curve25519.p) :
    curve25519.decodeU n = 0 ↔ n = 0 := by
  rw [curve25519.decodeU_of_lt (lt_of_lt_of_le h (by rw [curve25519.p_def]; omega)),
    ZMod.natCast_eq_zero_iff]
  exact ⟨fun hd => Nat.eq_zero_of_dvd_of_lt hd h, fun h0 => h0 ▸ dvd_zero _⟩

/-- If `x25519_scalarmult k u = ok r`, then `was_contributory r` returns
`!x25519_is_all_zero r`. -/
theorem was_contributory_refines (k u r : Array U8 32#usize)
    (hr : x25519_ref.x25519_scalarmult k u = ok r) :
    SharedSecret.was_contributory r ⦃ b =>
      (do
        let s ← x25519_ref.x25519_scalarmult k u
        let z ← x25519_ref.x25519_is_all_zero s
        ok (!z)) = ok b ⦄ := by
  have hlt : r.asNat 8 < curve25519.p := by
    obtain ⟨r', hr', hval⟩ := exists_ok_of_spec (x25519_scalarmult_spec k u)
    rw [hr, ok.injEq] at hr'; subst hr'
    rw [hval]; exact curve25519.x25519_lt _ _
  apply spec_mono (was_contributory_spec r)
  intro b hb
  have hz := decodeU_eq_zero_iff hlt
  rw [hr, bind_ok, is_all_zero_eq, bind_ok, ok.injEq]
  cases b <;> simp_all

/-- **`StaticSecret::diffie_hellman` and then `SharedSecret::was_contributory` refines the
reference.** It returns `!x25519_is_all_zero (x25519_scalarmult k u)`. -/
theorem static_diffie_hellman_was_contributory_refines (k u : Array U8 32#usize) :
    (do
      let ss ← StaticSecret.diffie_hellman k u
      SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let s ← x25519_ref.x25519_scalarmult k u
        let z ← x25519_ref.x25519_is_all_zero s
        ok (!z)) = ok b ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (static_diffie_hellman_refines k u)
  rw [hr, bind_ok]
  exact was_contributory_refines k u r hspec

/-- As `static_diffie_hellman_was_contributory_refines`, for `EphemeralSecret`. -/
theorem ephemeral_diffie_hellman_was_contributory_refines (k u : Array U8 32#usize) :
    (do
      let ss ← EphemeralSecret.diffie_hellman k u
      SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let s ← x25519_ref.x25519_scalarmult k u
        let z ← x25519_ref.x25519_is_all_zero s
        ok (!z)) = ok b ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (ephemeral_diffie_hellman_refines k u)
  rw [hr, bind_ok]
  exact was_contributory_refines k u r hspec

/-- As `static_diffie_hellman_was_contributory_refines`, for `ReusableSecret`. -/
theorem reusable_diffie_hellman_was_contributory_refines (k u : Array U8 32#usize) :
    (do
      let ss ← ReusableSecret.diffie_hellman k u
      SharedSecret.was_contributory ss) ⦃ b =>
      (do
        let s ← x25519_ref.x25519_scalarmult k u
        let z ← x25519_ref.x25519_is_all_zero s
        ok (!z)) = ok b ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (reusable_diffie_hellman_refines k u)
  rw [hr, bind_ok]
  exact was_contributory_refines k u r hspec

/-! ## Drop

x25519-dalek 3.0.0 has an explicit `Drop` impl for `EphemeralSecret`, `ReusableSecret`,
`StaticSecret` and `SharedSecret`. With the feature `zeroize`, each `drop` calls `zeroize` on
the 32 bytes. Aeneas translates the four `drop` functions. It does not translate the calls to
them: Charon's output for `EphemeralSecret::diffie_hellman` drops `self` at the end, and the
Lean body has no such call. Rust `drop` takes `&mut self` and returns `()`. Aeneas
models it as a function that returns the new value of `self`. So the theorems below state that
new value. `ephemeral_diffie_hellman_drop_refines` states a hand-written sequence: the body of
`EphemeralSecret::diffie_hellman` followed by the drop of `self`, in the order of the Rust
program. Lean values have no memory, so these theorems do not state that the old bytes are gone
from memory. -/

/-- The `zeroize` of a byte array, with the trait arguments of the translation, gives 32 zero
bytes (the fork's `RustAx.zeroize`). -/
theorem zeroize_bytes_spec (s : Array U8 32#usize) :
    x25519_dalek.Array.Insts.ZeroizeZeroize.zeroize
      (x25519_dalek.zeroize.Zeroize.Blanket x25519_dalek.U8.Insts.ZeroizeDefaultIsZeroes) s
      ⦃ r => r = Array.repeat 32#usize 0#u8 ⦄ :=
  Curve25519Dalek.Array.Insts.ZeroizeZeroize.zeroize_U8_spec s

/-- `Drop for StaticSecret` gives a new value of `self` that is 32 zero bytes. -/
theorem static_secret_drop_spec (s : Array U8 32#usize) :
    StaticSecret.Insts.CoreOpsDropDrop.drop s ⦃ r => r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold StaticSecret.Insts.CoreOpsDropDrop.drop
  simpa using zeroize_bytes_spec s

/-- `Drop for ReusableSecret` gives a new value of `self` that is 32 zero bytes. -/
theorem reusable_secret_drop_spec (s : Array U8 32#usize) :
    ReusableSecret.Insts.CoreOpsDropDrop.drop s ⦃ r => r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold ReusableSecret.Insts.CoreOpsDropDrop.drop
  simpa using zeroize_bytes_spec s

/-- `Drop for EphemeralSecret` gives a new value of `self` that is 32 zero bytes. -/
theorem ephemeral_secret_drop_spec (s : Array U8 32#usize) :
    EphemeralSecret.Insts.CoreOpsDropDrop.drop s ⦃ r => r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold EphemeralSecret.Insts.CoreOpsDropDrop.drop
  simpa using zeroize_bytes_spec s

/-- `Drop for SharedSecret` gives a new value of `self` that is 32 zero bytes (the fork's
`zeroize` of `MontgomeryPoint`). -/
theorem shared_secret_drop_spec (s : Array U8 32#usize) :
    SharedSecret.Insts.CoreOpsDropDrop.drop s ⦃ r => r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold SharedSecret.Insts.CoreOpsDropDrop.drop
  simpa using Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize_spec s

/-- `Zeroize for PublicKey` gives a new value of `self` that is 32 zero bytes. -/
theorem public_key_zeroize_spec (p : Array U8 32#usize) :
    PublicKey.Insts.ZeroizeZeroize.zeroize p ⦃ r => r = Array.repeat 32#usize 0#u8 ⦄ := by
  unfold PublicKey.Insts.ZeroizeZeroize.zeroize
  simpa using Curve25519Dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize.zeroize_spec p

/-- **`EphemeralSecret::diffie_hellman` with the drop of `self` refines the reference.** The
sequence is hand-written, because the translation erases the drop call. The body returns the
bytes of `x25519_scalarmult k u`, and the drop then gives 32 zero bytes as the new value of
`self`. In Rust, `diffie_hellman` passes a copy of the secret bytes to `mul_clamped`. This
theorem says nothing about that copy. -/
theorem ephemeral_diffie_hellman_drop_refines (k u : Array U8 32#usize) :
    (do
      let ss ← EphemeralSecret.diffie_hellman k u
      let k' ← EphemeralSecret.Insts.CoreOpsDropDrop.drop k
      ok (ss, k')) ⦃ p =>
      x25519_ref.x25519_scalarmult k u = ok p.1 ∧ p.2 = Array.repeat 32#usize 0#u8 ⦄ := by
  obtain ⟨r, hr, hspec⟩ := exists_ok_of_spec (ephemeral_diffie_hellman_refines k u)
  obtain ⟨z, hz, hzero⟩ := exists_ok_of_spec (ephemeral_secret_drop_spec k)
  rw [hr, bind_ok, hz, bind_ok, spec_ok]
  exact ⟨hspec, hzero⟩

end ForkSim
