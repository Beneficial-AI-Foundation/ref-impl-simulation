/-
Pilot, part 2: the HPKE key schedule (RFC 9180 §5.1) in base mode.
Reference `Ref.KeySchedule` against real `Real.Hpke.key_schedule`.
-/
module
public import Sim.Kdf
public import Sim.Rel
import all Aeneas.Std.String
@[expose] public section
open Aeneas Aeneas.Std Result WP
set_option linter.unusedSimpArgs false

namespace Sim

/-! ### Reference-side closed forms -/

theorem ref_lit (n : Usize) (l : List U8) (hl : l.length = n.val) :
    (do
      let s ← lift (Array.to_slice (Array.make n l hl))
      let v ← Ref.hacspec_lib.byte_vec s
      Ref.hacspec_lib.Seq.from_vec core.clone.CloneU8 v) ⦃ s => s.b.val = l ⦄ := by
  unfold Ref.hacspec_lib.byte_vec Ref.hacspec_lib.Seq.from_vec
  simp only [lift, bind_ok]
  apply spec_bind (alloc.slice.Slice.to_vec_spec _ _ (by intro x _; exact cloneU8_ok x))
  intro v hv
  simp [alloc.vec.Vec.val, ← hv, Array.to_slice]

theorem ref_lit_bind {γ : Type} (n : Usize) (l : List U8) (hl : l.length = n.val)
    (k : Ref.hacspec_lib.Seq U8 → Result γ) (P : γ → Prop)
    (hk : ∀ s : Ref.hacspec_lib.Seq U8, s.b.val = l → k s ⦃ P ⦄) :
    (do
      let s ← lift (Array.to_slice (Array.make n l hl))
      let v ← Ref.hacspec_lib.byte_vec s
      let s1 ← Ref.hacspec_lib.Seq.from_vec core.clone.CloneU8 v
      k s1) ⦃ P ⦄ := by
  unfold Ref.hacspec_lib.byte_vec Ref.hacspec_lib.Seq.from_vec
  simp only [lift, bind_ok]
  apply spec_bind (alloc.slice.Slice.to_vec_spec _ _ (by intro x _; exact cloneU8_ok x))
  intro v hv
  apply hk
  simp [alloc.vec.Vec.val, ← hv, Array.to_slice]

theorem ref_concat_owned (a b : Ref.hacspec_lib.Seq U8)
    (h : a.b.val.length + b.b.val.length ≤ Usize.max) :
    Ref.hacspec_lib.Seq.concat_owned core.clone.CloneU8 a b ⦃ r => r.b.val = a.b.val ++ b.b.val ⦄ := by
  unfold Ref.hacspec_lib.Seq.concat_owned
  apply spec_bind (extend_u8 _ _ (by simpa using h))
  intro r hr
  simp [hr]

theorem ref_empty_bytes : Ref.empty_bytes ⦃ s => s.b.val = [] ⦄ := by
  unfold Ref.empty_bytes Ref.hacspec_lib.Seq.new
  simp only [bind_ok]
  apply spec_bind (alloc.vec.from_elem_spec _ _ _ (cloneU8_ok _))
  intro v hv
  simp [hv.1]


def refKemU16 : Ref.hpke_kem.KEM → U16
  | .DHKEM_P256_HKDF_SHA256 => 16#u16
  | .DHKEM_P384_HKDF_SHA384 => 17#u16
  | .DHKEM_P521_HKDF_SHA512 => 18#u16
  | .DHKEM_X25519_HKDF_SHA256 => 32#u16
  | .DHKEM_X448_HKDF_SHA512 => 33#u16

def refKdfU16 : Ref.hpke_kdf.KDF → U16
  | .HKDF_SHA256 => 1#u16
  | .HKDF_SHA384 => 2#u16
  | .HKDF_SHA512 => 3#u16

def refAeadU16 : Ref.hpke_aead.AEAD → U16
  | .AES_128_GCM => 1#u16
  | .AES_256_GCM => 2#u16
  | .ChaCha20Poly1305 => 3#u16
  | .Export_only => 65535#u16

def refNk : Ref.hpke_aead.AEAD → Nat
  | .AES_128_GCM => 16
  | .AES_256_GCM => 32
  | .ChaCha20Poly1305 => 32
  | .Export_only => 0

def refNn : Ref.hpke_aead.AEAD → Nat
  | .Export_only => 0
  | _ => 12

def hpkeStr : List U8 := [72#u8, 80#u8, 75#u8, 69#u8]

def suiteBytes (k : Ref.hpke_kem.KEM) (d : Ref.hpke_kdf.KDF) (a : Ref.hpke_aead.AEAD) : List U8 :=
  hpkeStr ++ be16 (refKemU16 k) ++ be16 (refKdfU16 d) ++ be16 (refAeadU16 a)

theorem be16_length (x : U16) : (be16 x).length = 2 := by simp [be16]

theorem ref_suite_id (m : Ref.Mode) (k : Ref.hpke_kem.KEM) (d : Ref.hpke_kdf.KDF) (a : Ref.hpke_aead.AEAD) :
    Ref.suite_id (m, k, d, a) ⦃ s => s.b.val = suiteBytes k d a ⦄ := by
  simp only [Ref.suite_id]
  apply ref_lit_bind; intro s1 hs1
  have hk : Ref.hpke_kem.kem_value k ⦃ v => v = refKemU16 k ⦄ := by
    cases k <;> simp [Ref.hpke_kem.kem_value, Ref.hacspec_lib.U16, refKemU16]
  have hd : Ref.hpke_kdf.kdf_value d ⦃ v => v = refKdfU16 d ⦄ := by
    cases d <;> simp [Ref.hpke_kdf.kdf_value, Ref.hacspec_lib.U16, refKdfU16]
  have ha : Ref.hpke_aead_value a ⦃ v => v = refAeadU16 a ⦄ := by
    cases a <;> simp [Ref.hpke_aead_value, Ref.hacspec_lib.U16, refAeadU16]
  apply spec_bind hk; intro i hi; subst hi
  apply spec_bind (ref_be16 _); intro s2 hs2
  apply spec_bind (ref_concat _ _ (by simp [hs1, hs2]; scalar_tac)); intro s3 hs3
  apply spec_bind hd; intro i1 hi1; subst hi1
  apply spec_bind (ref_be16 _); intro s4 hs4
  apply spec_bind (ref_concat _ _ (by simp [hs3, hs1, hs2, hs4]; scalar_tac)); intro s5 hs5
  apply spec_bind ha; intro i2 hi2; subst hi2
  apply spec_bind (ref_be16 _); intro s6 hs6
  apply spec_mono (ref_concat _ _ (by simp [hs5, hs3, hs1, hs2, hs4, hs6]; scalar_tac))
  intro r hr
  simp [hr, hs5, hs3, hs1, hs2, hs4, hs6, suiteBytes, be16, hpkeStr]

theorem ref_verify_base (k : Ref.hpke_kem.KEM) (d : Ref.hpke_kdf.KDF) (a : Ref.hpke_aead.AEAD)
    (psk psk_id : Ref.hacspec_lib.Seq U8) (h1 : psk.b.val = []) (h2 : psk_id.b.val = []) :
    Ref.VerifyPSKInputs (.mode_base, k, d, a) psk psk_id ⦃ r => r = .Ok () ⦄ := by
  unfold Ref.VerifyPSKInputs
  simp [Ref.hacspec_lib.Seq.len, alloc.vec.Vec.len, h1, h2, Ref.Mode.Insts.CoreCmpPartialEqMode.eq, Ref.Mode.read_discriminant]

/-! ### Configuration relation -/

inductive KemRel : Ref.hpke_kem.KEM → Real.hpke_rs_crypto.types.KemAlgorithm → Prop
  | p256 : KemRel .DHKEM_P256_HKDF_SHA256 .DhKemP256
  | p384 : KemRel .DHKEM_P384_HKDF_SHA384 .DhKemP384
  | p521 : KemRel .DHKEM_P521_HKDF_SHA512 .DhKemP521
  | x25519 : KemRel .DHKEM_X25519_HKDF_SHA256 .DhKem25519
  | x448 : KemRel .DHKEM_X448_HKDF_SHA512 .DhKem448

inductive KdfIdRel : Ref.hpke_kdf.KDF → Real.hpke_rs_crypto.types.KdfAlgorithm → Prop
  | sha256 : KdfIdRel .HKDF_SHA256 .HkdfSha256
  | sha384 : KdfIdRel .HKDF_SHA384 .HkdfSha384
  | sha512 : KdfIdRel .HKDF_SHA512 .HkdfSha512

inductive AeadRel : Ref.hpke_aead.AEAD → Real.hpke_rs_crypto.types.AeadAlgorithm → Prop
  | aes128 : AeadRel .AES_128_GCM .Aes128Gcm
  | aes256 : AeadRel .AES_256_GCM .Aes256Gcm
  | chacha : AeadRel .ChaCha20Poly1305 .ChaCha20Poly1305
  | export : AeadRel .Export_only .HpkeExport

theorem KdfIdRel.kdfRel {d rd} (h : KdfIdRel d rd) : KdfRel d rd := by
  cases h <;> rfl

theorem kem_disc {k rk} (h : KemRel k rk) : UScalar.cast .U16 (read_discriminant rk) = refKemU16 k := by
  cases h <;> rfl

theorem kdf_disc {d rd} (h : KdfIdRel d rd) : UScalar.cast .U16 (read_discriminant rd) = refKdfU16 d := by
  cases h <;> rfl

theorem aead_disc {a ra} (h : AeadRel a ra) : UScalar.cast .U16 (read_discriminant ra) = refAeadU16 a := by
  cases h <;> rfl

/-! ### Real-side closed forms -/

theorem real_ciphersuite {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (self : Real.Hpke C P E1 E2) (k : Ref.hpke_kem.KEM) (d : Ref.hpke_kdf.KDF) (a : Ref.hpke_aead.AEAD)
    (hk : KemRel k self.kem_id) (hd : KdfIdRel d self.kdf_id) (ha : AeadRel a self.aead_id) :
    Real.Hpke.ciphersuite inst self ⦃ v => v.val = suiteBytes k d a ⦄ := by
  unfold Real.Hpke.ciphersuite
  have h1 := core.num.U16.to_be_bytes.step_spec (UScalar.cast .U16 (read_discriminant self.kem_id))
  have h2 := core.num.U16.to_be_bytes.step_spec (UScalar.cast .U16 (read_discriminant self.kdf_id))
  have h3 := core.num.U16.to_be_bytes.step_spec (UScalar.cast .U16 (read_discriminant self.aead_id))
  simp only [lift, spec_ok] at h1 h2 h3
  simp only [lift, bind_ok]
  apply spec_mono (real_concat _ (by simp [Array.to_slice, h1, h2, h3]; scalar_tac))
  intro v hv
  rw [hv]
  simp only [kem_disc hk, kdf_disc hd, aead_disc ha] at h1 h2 h3 ⊢
  simp [Array.to_slice, h1, h2, h3, suiteBytes, be16, hpkeStr]

theorem real_verify_base {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (self : Real.Hpke C P E1 E2) (hm : self.mode = .Base) (psk psk_id : Slice U8)
    (h1 : psk.val = []) (h2 : psk_id.val = []) :
    Real.Hpke.verify_psk_inputs inst self psk psk_id ⦃ r => r = .Ok () ⦄ := by
  unfold Real.Hpke.verify_psk_inputs
  simp [core.slice.Slice.is_empty, h1, h2, hm, Real.Mode.Insts.CoreCmpPartialEqMode.eq,
    Real.Mode.read_discriminant]

/-! ### Labels. The real side holds `&str` literals as `toStr "..."`, whose bytes the kernel
cannot compute (`String.toByteArray`); we evaluate them with `native_decide`. -/

def lPskIdHash : List U8 := [112#u8, 115#u8, 107#u8, 95#u8, 105#u8, 100#u8, 95#u8, 104#u8, 97#u8, 115#u8, 104#u8]
def lInfoHash : List U8 := [105#u8, 110#u8, 102#u8, 111#u8, 95#u8, 104#u8, 97#u8, 115#u8, 104#u8]
def lSecret : List U8 := [115#u8, 101#u8, 99#u8, 114#u8, 101#u8, 116#u8]
def lKey : List U8 := [107#u8, 101#u8, 121#u8]
def lBaseNonce : List U8 := [98#u8, 97#u8, 115#u8, 101#u8, 95#u8, 110#u8, 111#u8, 110#u8, 99#u8, 101#u8]
def lExp : List U8 := [101#u8, 120#u8, 112#u8]

theorem str_psk_id_hash : (toStr "psk_id_hash").val = lPskIdHash := by simp [toStr]; native_decide
theorem str_info_hash : (toStr "info_hash").val = lInfoHash := by simp [toStr]; native_decide
theorem str_secret : (toStr "secret").val = lSecret := by simp [toStr]; native_decide
theorem str_key : (toStr "key").val = lKey := by simp [toStr]; native_decide
theorem str_base_nonce : (toStr "base_nonce").val = lBaseNonce := by simp [toStr]; native_decide
theorem str_exp : (toStr "exp").val = lExp := by simp [toStr]; native_decide

theorem ref_psk_id_hash_label : Ref.psk_id_hash_label ⦃ s => s.b.val = lPskIdHash ⦄ := ref_lit _ _ _
theorem ref_info_hash_label : Ref.info_hash_label ⦃ s => s.b.val = lInfoHash ⦄ := ref_lit _ _ _
theorem ref_secret_label : Ref.secret_label ⦃ s => s.b.val = lSecret ⦄ := ref_lit _ _ _
theorem ref_key_label : Ref.key_label ⦃ s => s.b.val = lKey ⦄ := ref_lit _ _ _
theorem ref_base_nonce_label : Ref.base_nonce_label ⦃ s => s.b.val = lBaseNonce ⦄ := ref_lit _ _ _
theorem ref_exp_label : Ref.exp_label ⦃ s => s.b.val = lExp ⦄ := ref_lit _ _ _

theorem ref_mode_label_base : Ref.hpke_mode_label .mode_base ⦃ s => s.b.val = [0#u8] ⦄ := by
  simp only [Ref.hpke_mode_label]; exact ref_lit _ _ _

/-- Key-schedule context as the real code builds it (mode byte, then the two labeled
extracts with salt `[0x00]`). -/
theorem real_ksc {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (self : Real.Hpke C P E1 E2) (hX : ExtractIsShared inst self.kdf_id) (hm : self.mode = .Base)
    (info psk_id suite : Slice U8)
    (h : 100 + suite.val.length + info.val.length + psk_id.val.length ≤ Usize.max) :
    Real.Hpke.key_schedule_context inst self info psk_id suite ⦃ r =>
      ∃ v, r = .Ok v ∧ v.val = [0#u8] ++
        (Shared.extract (kdfHash self.kdf_id) [0#u8] (hpkeV1 ++ suite.val ++ lPskIdHash ++ psk_id.val)).val ++
        (Shared.extract (kdfHash self.kdf_id) [0#u8] (hpkeV1 ++ suite.val ++ lInfoHash ++ info.val)).val ⦄ := by
  unfold Real.Hpke.key_schedule_context
  simp only [lift, bind_ok]
  apply spec_bind (real_labeled_extract inst _ hX _ _ _ _
    (by simp [str_psk_id_hash, lPskIdHash, hpkeV1]; omega)); intro r1 hr1
  subst hr1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (real_labeled_extract inst _ hX _ _ _ _
    (by simp [str_info_hash, lInfoHash, hpkeV1]; omega)); intro r2 hr2
  subst hr2
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hm]
  apply spec_bind (real_concat _ (by
    have : Shared.hashLen (kdfHash self.kdf_id) ≤ 64 := by
      cases self.kdf_id <;> simp [kdfHash, Shared.hashLen]
    simp [Array.to_slice, Shared.extract_length]
    scalar_tac))
  intro v hv
  simp only [spec_ok]
  refine ⟨v, rfl, ?_⟩
  rw [hv]
  have h0 : UScalar.cast UScalarTy.U8 (read_discriminant Real.Mode.Base) = 0#u8 := by rfl
  simp [Array.to_slice, h0]
  rw [str_psk_id_hash, str_info_hash]

/-! ### Lengths -/

def stdNk : Real.hpke_rs_crypto.types.AeadAlgorithm → Usize
  | .Aes128Gcm => 16#usize
  | .Aes256Gcm => 32#usize
  | .ChaCha20Poly1305 => 32#usize
  | .HpkeExport => 0#usize

def stdNn : Real.hpke_rs_crypto.types.AeadAlgorithm → Usize
  | .HpkeExport => 0#usize
  | _ => 12#usize

def stdNh : Real.hpke_rs_crypto.types.KdfAlgorithm → Usize
  | .HkdfSha256 => 32#usize
  | .HkdfSha384 => 48#usize
  | .HkdfSha512 => 64#usize

/-- The provider uses the RFC 9180 lengths (the trait's default methods). -/
def LengthsStd {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2) : Prop :=
  (∀ a, inst.aead_key_length a = ok (stdNk a)) ∧
  (∀ a, inst.aead_nonce_length a = ok (stdNn a)) ∧
  (∀ d, inst.kdf_digest_length d = ok (stdNh d))

theorem ref_Nk (a : Ref.hpke_aead.AEAD) (ra) (h : AeadRel a ra) :
    Ref.hpke_aead.Nk a ⦃ n => n = stdNk ra ⦄ := by
  cases h <;> simp [Ref.hpke_aead.Nk, stdNk]

theorem ref_Nn (a : Ref.hpke_aead.AEAD) (ra) (h : AeadRel a ra) :
    Ref.hpke_aead.Nn a ⦃ n => n = stdNn ra ⦄ := by
  cases h <;> simp [Ref.hpke_aead.Nn, stdNn]

theorem ref_Nh (d : Ref.hpke_kdf.KDF) (rd) (h : KdfIdRel d rd) :
    Ref.hpke_kdf.Nh d ⦃ n => n = stdNh rd ⦄ := by
  cases h <;> simp [Ref.hpke_kdf.Nh, stdNh]

theorem stdNk_le (d : Ref.hpke_kdf.KDF) (ra) : (stdNk ra).val ≤ 255 * nhRef d := by
  cases ra <;> cases d <;> simp [stdNk, nhRef]
theorem stdNn_le (d : Ref.hpke_kdf.KDF) (ra) : (stdNn ra).val ≤ 255 * nhRef d := by
  cases ra <;> cases d <;> simp [stdNn, nhRef]
theorem stdNh_le (d : Ref.hpke_kdf.KDF) (rd) (h : KdfIdRel d rd) : (stdNh rd).val ≤ 255 * nhRef d := by
  cases h <;> simp [stdNh, nhRef]

/-! ### The key schedule -/

/-- Output relation on the encryption context. The real context also carries a fresh
`Hpke` value (with a new PRNG); the reference context has none. -/
def CtxRel {C P E1 E2 : Type} (c : Real.Context C P E1 E2)
    (t : Ref.hacspec_lib.Seq U8 × Ref.hacspec_lib.Seq U8 × U32 × Ref.hacspec_lib.Seq U8) : Prop :=
  c.key.val = t.1.b.val ∧ c.nonce.val = t.2.1.b.val ∧
  c.sequence_number.val = t.2.2.1.val ∧ c.exporter_secret.val = t.2.2.2.b.val

/-- Output relation of the key schedule: both succeed, and the contexts agree. -/
def KsRel {C P E1 E2 : Type}
    (r : core.result.Result (Real.Context C P E1 E2) Real.HpkeError)
    (s : core.result.Result (Ref.hacspec_lib.Seq U8 × Ref.hacspec_lib.Seq U8 × U32 × Ref.hacspec_lib.Seq U8)
      Ref.hpke_errors.HpkeError) : Prop :=
  ∃ c t, r = .Ok c ∧ s = .Ok t ∧ CtxRel c t

@[simp] theorem monad_bind_ok {α β : Type} (x : α) (f : α → Result β) : (ok x >>= f) = f x := bind_ok x f

theorem kdf_sha256 {d rd} (hS : d = Ref.hpke_kdf.KDF.HKDF_SHA256) (h : KdfIdRel d rd) :
    rd = .HkdfSha256 := by
  subst hS; cases h; rfl

theorem key_schedule_base_refines {C P E1 E2 : Type}
    (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (self : Real.Hpke C P E1 E2) (hm : self.mode = .Base)
    (hX : ExtractIsShared inst self.kdf_id) (hE : ExpandIsShared inst self.kdf_id)
    (hL : LengthsStd inst) (hP : ∃ p, inst.prng = ok p)
    (k : Ref.hpke_kem.KEM) (d : Ref.hpke_kdf.KDF) (a : Ref.hpke_aead.AEAD) (hS : d = .HKDF_SHA256)
    (hk : KemRel k self.kem_id) (hd : KdfIdRel d self.kdf_id) (ha : AeadRel a self.aead_id)
    (ss info psk psk_id : Slice U8) (rss rinfo rpsk rpsk_id : Ref.hacspec_lib.Seq U8)
    (h1 : rss.b.val = ss.val) (h2 : rinfo.b.val = info.val)
    (hpsk : psk.val = []) (hpsk_id : psk_id.val = [])
    (hrpsk : rpsk.b.val = []) (hrpsk_id : rpsk_id.b.val = [])
    (hinfo : 200 + info.val.length ≤ Usize.max) :
    rel (Real.Hpke.key_schedule inst self ss info psk psk_id)
        (Ref.KeySchedule (.mode_base, k, d, a) rss rinfo rpsk rpsk_id) KsRel := by
  have hkdf : self.kdf_id = .HkdfSha256 := kdf_sha256 hS hd
  have hNh : Shared.hashLen (kdfHash self.kdf_id) = 32 := by rw [hkdf]; rfl
  unfold Real.Hpke.key_schedule Ref.KeySchedule
  -- real: verify, ciphersuite, key-schedule context
  apply rel_bind_left (real_verify_base inst self hm psk psk_id hpsk hpsk_id); intro r hr; subst hr
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply rel_bind_left (real_ciphersuite inst self k d a hk hd ha); intro suite hsuite
  have hsl : suite.val.length = 10 := by simp [hsuite, suiteBytes, hpkeStr, be16_length]
  apply rel_bind_left (real_ksc inst self hX hm info psk_id (alloc.vec.Vec.deref suite)
    (by simp [hsl, hpsk_id]; omega))
  rintro r1 ⟨ksc, hr1, hksc⟩; subst hr1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- reference: verify, suite_id, labels, two extracts, context
  apply rel_bind_right (ref_verify_base k d a rpsk rpsk_id hrpsk hrpsk_id); intro r hr; subst hr
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply rel_bind_right (ref_suite_id .mode_base k d a); intro rs hrs
  apply rel_bind_right ref_empty_bytes; intro re hre
  apply rel_bind_right ref_psk_id_hash_label; intro l1 hl1
  apply rel_bind_right (ref_labeled_extract d hS rs re l1 rpsk_id
    (by simp [hrs, hl1, hrpsk_id, suiteBytes, hpkeStr, be16_length, lPskIdHash, hpkeV1]; scalar_tac))
  intro x1 hx1; subst hx1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply rel_bind_right ref_info_hash_label; intro l2 hl2
  apply rel_bind_right (ref_labeled_extract d hS rs re l2 rinfo
    (by simp [hrs, hl2, h2, suiteBytes, hpkeStr, be16_length, lInfoHash, hpkeV1]; omega))
  intro x2 hx2; subst hx2
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply rel_bind_right ref_mode_label_base; intro ml hml
  have hextR : ∀ (salt ikm : List U8), (Shared.extract (refHash d) salt ikm).val.length ≤ 64 := by
    intro salt ikm; rw [Shared.extract_length]; cases d <;> simp [refHash, Shared.hashLen]
  have hmax : (200 : Nat) ≤ Usize.max := by scalar_tac
  apply rel_bind_right (ref_concat_owned _ _ (by
    have := hextR re.b.val (hpkeV1 ++ rs.b.val ++ l1.b.val ++ rpsk_id.b.val)
    simp only [hml, List.length_singleton]; omega)); intro c1 hc1
  apply rel_bind_right (ref_concat_owned _ _ (by
    have := hextR re.b.val (hpkeV1 ++ rs.b.val ++ l1.b.val ++ rpsk_id.b.val)
    have := hextR re.b.val (hpkeV1 ++ rs.b.val ++ l2.b.val ++ rinfo.b.val)
    simp only [hc1, hml, List.length_append, List.length_singleton]; omega)); intro c2 hc2
  apply rel_bind_right ref_secret_label; intro l3 hl3
  -- lockstep: the secret
  apply rel_bind_left (real_labeled_extract inst _ hX ss _ _ psk
    (by simp [hsl, str_secret, lSecret, hpsk, hpkeV1]; omega)); intro r2 hr2; subst hr2
  simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply rel_bind_right (ref_labeled_extract d hS rs rss l3 rpsk
    (by simp [hrs, hl3, hrpsk, suiteBytes, hpkeStr, be16_length, lSecret, hpkeV1]; omega))
  intro x3 hx3; subst hx3
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- the facts that relate the two states at this point
  have hk1 : refHash d = kdfHash self.kdf_id := hd.kdfRel
  have hctx : c2.b.val = ksc.val := by
    rw [hksc, hc2, hc1, hml, hre, hl1, hl2, hrpsk_id, hrs, h2, hk1, ← hsuite, hpsk_id,
      Shared.extract_salt_zero, Shared.extract_salt_zero]
    simp
  have hprk : (Shared.extract (refHash d) rss.b.val (hpkeV1 ++ rs.b.val ++ l3.b.val ++ rpsk.b.val)).val =
      (Shared.extract (kdfHash self.kdf_id) ss.val
        (hpkeV1 ++ (alloc.vec.Vec.deref suite).val ++ (toStr "secret").val ++ psk.val)).val := by
    rw [hk1, h1, hrs, hl3, str_secret, hrpsk, hpsk, deref_val, hsuite]
  have hkscl : ksc.val.length ≤ 129 := by
    have e1 := hextR [] (hpkeV1 ++ suiteBytes k d a ++ lPskIdHash ++ [])
    have e2 := hextR [] (hpkeV1 ++ suiteBytes k d a ++ lInfoHash ++ info.val)
    rw [← hctx, hc2, hc1, hml, hre, hl1, hl2, hrpsk_id, hrs, h2]
    simp only [List.length_append, List.length_singleton]; omega
  -- lockstep: key
  rw [hL.1]; simp only [bind_ok]
  apply rel_bind_left (real_labeled_expand inst _ hE _ _ _ _ _
    (by rw [deref_val, Shared.extract_length]) (by cases self.aead_id <;> simp [stdNk]) (by simp [hsl, str_key, lKey, hpkeV1]; omega))
  intro r4 hr4
  apply rel_bind_right ref_key_label; intro l4 hl4
  apply rel_bind_right (ref_Nk a _ ha); intro n4 hn4; subst hn4
  apply rel_bind_right (ref_labeled_expand d hS rs _ l4 c2 _ (stdNk_le d _)
    (by simp [hrs, hl4, hctx, suiteBytes, hpkeStr, be16_length, lKey, hpkeV1]; omega))
  intro x4 hx4; subst hx4
  simp only [deref_val, hsuite, hrs, hl4, str_key, hctx, hk1, h1, hl3, hrpsk, hpsk, str_secret] at hr4 ⊢
  rcases hEk : Shared.expand (kdfHash self.kdf_id)
      (Shared.extract (kdfHash self.kdf_id) ss.val (hpkeV1 ++ suiteBytes k d a ++ lSecret ++ [])).val
      (be16 (UScalar.cast UScalarTy.U16 (stdNk self.aead_id)) ++ hpkeV1 ++ suiteBytes k d a ++ lKey ++ ksc.val)
      (stdNk self.aead_id).val with _ | vk
  · exact absurd hEk (Shared.expand_ne_none _ _ _ _ (by
      rw [hNh]; cases self.aead_id <;> simp [stdNk]))
  rw [hEk] at hr4; simp only at hr4; subst hr4
  simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- lockstep: base nonce
  rw [hL.2.1]; simp only [bind_ok]
  apply rel_bind_left (real_labeled_expand inst _ hE _ _ _ _ _
    (by rw [deref_val, Shared.extract_length]) (by cases self.aead_id <;> simp [stdNn]) (by simp [hsl, str_base_nonce, lBaseNonce, hpkeV1]; omega))
  intro r6 hr6
  apply rel_bind_right ref_base_nonce_label; intro l5 hl5
  apply rel_bind_right (ref_Nn a _ ha); intro n5 hn5; subst hn5
  apply rel_bind_right (ref_labeled_expand d hS rs _ l5 c2 _ (stdNn_le d _)
    (by simp [hrs, hl5, hctx, suiteBytes, hpkeStr, be16_length, lBaseNonce, hpkeV1]; omega))
  intro x5 hx5; subst hx5
  simp only [deref_val, hsuite, hrs, hl5, str_base_nonce, hctx, hk1, h1, hl3, hrpsk, hpsk, str_secret] at hr6 ⊢
  rcases hEn : Shared.expand (kdfHash self.kdf_id)
      (Shared.extract (kdfHash self.kdf_id) ss.val (hpkeV1 ++ suiteBytes k d a ++ lSecret ++ [])).val
      (be16 (UScalar.cast UScalarTy.U16 (stdNn self.aead_id)) ++ hpkeV1 ++ suiteBytes k d a ++ lBaseNonce ++ ksc.val)
      (stdNn self.aead_id).val with _ | vn
  · exact absurd hEn (Shared.expand_ne_none _ _ _ _ (by
      rw [hNh]; cases self.aead_id <;> simp [stdNn]))
  rw [hEn] at hr6; simp only at hr6; subst hr6
  simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- lockstep: exporter secret
  rw [hL.2.2]; simp only [bind_ok]
  apply rel_bind_left (real_labeled_expand inst _ hE _ _ _ _ _
    (by rw [deref_val, Shared.extract_length]) (by cases self.kdf_id <;> simp [stdNh]) (by simp [hsl, str_exp, lExp, hpkeV1]; omega))
  intro r8 hr8
  apply rel_bind_right ref_exp_label; intro l6 hl6
  apply rel_bind_right (ref_Nh d _ hd); intro n6 hn6; subst hn6
  apply rel_bind_right (ref_labeled_expand d hS rs _ l6 c2 _ (stdNh_le d _ hd)
    (by simp [hrs, hl6, hctx, suiteBytes, hpkeStr, be16_length, lExp, hpkeV1]; omega))
  intro x6 hx6; subst hx6
  simp only [deref_val, hsuite, hrs, hl6, str_exp, hctx, hk1, h1, hl3, hrpsk, hpsk, str_secret] at hr8 ⊢
  rcases hEe : Shared.expand (kdfHash self.kdf_id)
      (Shared.extract (kdfHash self.kdf_id) ss.val (hpkeV1 ++ suiteBytes k d a ++ lSecret ++ [])).val
      (be16 (UScalar.cast UScalarTy.U16 (stdNh self.kdf_id)) ++ hpkeV1 ++ suiteBytes k d a ++ lExp ++ ksc.val)
      (stdNh self.kdf_id).val with _ | ve
  · exact absurd hEe (Shared.expand_ne_none _ _ _ _ (by
      rw [hNh]; cases self.kdf_id <;> simp [stdNh]))
  rw [hEe] at hr8; simp only at hr8; subst hr8
  simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  -- the real side clones the configuration (fresh PRNG); nothing on the reference side
  obtain ⟨p, hp⟩ := hP
  simp only [Real.Hpke.Insts.CoreCloneClone.clone, hp, bind_ok]
  apply rel_ok
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
end Sim
