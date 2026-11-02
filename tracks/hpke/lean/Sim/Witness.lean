/-
The premises of `key_schedule_base_refines` can hold together. `inst` is a provider that
computes HKDF with the shared model and fails on every other operation. With it, the
theorem applies to the suite DHKEM(X25519, HKDF-SHA256), HKDF-SHA256, AES-128-GCM.
-/
module
public import Sim.KeySchedule
@[expose] public section
open Aeneas Aeneas.Std Result

namespace Sim.Witness
open Real.hpke_rs_crypto

def errInst : core.error.Error Unit := ⟨⟨fun _ _ => fail .panic⟩, ⟨fun _ _ => fail .panic⟩⟩

def tryRng0 : Real.rand_core.TryRng Unit Never :=
  { coreerrorErrorInst := ⟨⟨fun _ _ => fail .panic⟩, ⟨fun _ _ => fail .panic⟩⟩,
    try_next_u32 := fun _ => fail .panic, try_next_u64 := fun _ => fail .panic,
    try_fill_bytes := fun _ _ => fail .panic }

def tryRng : Real.rand_core.TryRng Unit Unit :=
  { coreerrorErrorInst := errInst, try_next_u32 := fun _ => fail .panic,
    try_next_u64 := fun _ => fail .panic, try_fill_bytes := fun _ _ => fail .panic }

/-- A provider whose HKDF is the shared model. -/
def inst : HpkeCrypto Unit Unit Unit Unit where
  corefmtDebugInst := ⟨fun _ _ => fail .panic⟩
  rand_coreCryptoRngInst :=
    ⟨⟨tryRng0, fun _ => fail .panic, fun _ => fail .panic, fun _ _ => fail .panic⟩, ⟨tryRng⟩⟩
  HpkeTestRngInst :=
    ⟨⟨fun _ _ => fail .panic⟩, ⟨fun _ _ => fail .panic⟩, fun _ _ => fail .panic, fun _ _ => fail .panic⟩
  zeroizeZeroizeInst := ⟨fun _ => fail .panic⟩
  «name» := fail .panic
  supports_kdf := fun _ => fail .panic
  supports_kem := fun _ => fail .panic
  supports_aead := fun _ => fail .panic
  prng := ok ()
  kdf_digest_length := fun d => ok (stdNh d)
  kdf_extract := fun alg salt ikm => ok (.Ok (Shared.extract (kdfHash alg) salt.val ikm.val))
  kdf_expand := fun alg prk info len =>
    ok (match Shared.expand (kdfHash alg) prk.val info.val len.val with
        | some v => .Ok v
        | none => .Err .HpkeInvalidOutputLength)
  dh := fun _ _ _ => fail .panic
  secret_to_public := fun _ _ => fail .panic
  kem_key_gen := fun _ _ => fail .panic
  kem_key_gen_derand := fun _ _ => fail .panic
  kem_encaps := fun _ _ _ => fail .panic
  kem_decaps := fun _ _ _ => fail .panic
  dh_validate_sk := fun _ _ => fail .panic
  aead_seal := fun _ _ _ _ _ => fail .panic
  aead_open := fun _ _ _ _ _ => fail .panic
  aead_key_length := fun a => ok (stdNk a)
  aead_nonce_length := fun a => ok (stdNn a)

theorem hX : ExtractIsShared inst .HkdfSha256 := fun _ _ => rfl

theorem hE : ExpandIsShared inst .HkdfSha256 := by
  intro prk info len _
  refine ⟨_, rfl, ?_⟩
  cases Shared.expand (kdfHash .HkdfSha256) prk.val info.val len.val <;> simp

theorem hL : LengthsStd inst := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def self0 : Real.Hpke Unit Unit Unit Unit :=
  { mode := .Base, kem_id := .DhKem25519, kdf_id := .HkdfSha256, aead_id := .Aes128Gcm, prng := () }

def emptyS : Slice U8 := (Std.Array.empty U8).to_slice
def emptyR : Ref.hacspec_lib.Seq U8 := ⟨alloc.vec.Vec.new U8⟩
theorem eS : emptyS.val = [] := Sim.empty_to_slice_val
theorem eR : emptyR.b.val = [] := by
  simp [emptyR, alloc.vec.Vec.new, alloc.vec.Vec.val, alloc.vec.Vec.from]

/-- The key schedule theorem, applied to `inst` and empty inputs. -/
theorem key_schedule_instance :
    rel (Real.Hpke.key_schedule inst self0 emptyS emptyS emptyS emptyS)
      (Ref.KeySchedule (.mode_base, .DHKEM_X25519_HKDF_SHA256, .HKDF_SHA256, .AES_128_GCM)
        emptyR emptyR emptyR emptyR) KsRel :=
  key_schedule_base_refines inst self0 rfl hX hE hL ⟨(), rfl⟩
    .DHKEM_X25519_HKDF_SHA256 .HKDF_SHA256 .AES_128_GCM rfl .x25519 .sha256 .aes128
    emptyS emptyS emptyS emptyS emptyR emptyR emptyR emptyR
    (by rw [eR, eS]) (by rw [eR, eS]) eS eS eR eR (by rw [eS]; scalar_tac)

end Sim.Witness
