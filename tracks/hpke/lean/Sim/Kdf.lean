/-
Pilot simulation theorems for HPKE (RFC 9180) LabeledExtract / LabeledExpand.
Reference: hacspec hpke-spec (Ref.*). Real: hpke-rs, generic in `HpkeCrypto` (Real.*).
Both sides bottom out in the shared HKDF model `Shared.*`.
-/
module
public import Ref
public import Real
@[expose] public section
open Aeneas Aeneas.Std Result WP

namespace Sim

theorem cloneU8_ok (x : U8) : core.clone.CloneU8.clone x = ok x := by
  simp

theorem list_clone_u8 (l : List U8) :
    List.clone core.clone.CloneU8.clone l ⦃ l' => l'.val = l ⦄ := by
  apply spec_mono (List.clone_spec (by intro x _; exact cloneU8_ok x))
  intro r h; exact h.1

theorem extend_u8 (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos h]
  apply spec_bind (list_clone_u8 _)
  intro l hl
  simp [hl]

end Sim

namespace Sim
theorem vec_clone_u8 (v : alloc.vec.Vec U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v ⦃ r => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply spec_bind (Slice.clone_spec (by intro x _; exact cloneU8_ok x))
  intro s hs
  simp only [spec_ok]
  cases v; simp at hs; simp [hs]

@[simp] theorem deref_val (v : alloc.vec.Vec U8) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]

theorem ref_concat (a b : Ref.hacspec_lib.Seq U8)
    (h : a.b.val.length + b.b.val.length ≤ Usize.max) :
    Ref.hacspec_lib.Seq.concat core.clone.CloneU8 a b ⦃ r => r.b.val = a.b.val ++ b.b.val ⦄ := by
  unfold Ref.hacspec_lib.Seq.concat
  apply spec_bind (vec_clone_u8 _)
  intro o ho; subst ho
  apply spec_bind (extend_u8 _ _ (by simpa using h))
  intro r hr
  simp [hr]

def hpkeV1 : List U8 := [72#u8, 80#u8, 75#u8, 69#u8, 45#u8, 118#u8, 49#u8]

theorem ref_version_label :
    Ref.hpke_kdf.hpke_version_label ⦃ s => s.b.val = hpkeV1 ⦄ := by
  unfold Ref.hpke_kdf.hpke_version_label Ref.hacspec_lib.byte_vec Ref.hacspec_lib.Seq.from_vec
  simp only [lift, bind_ok]
  apply spec_bind (alloc.slice.Slice.to_vec_spec _ _ (by intro x _; exact cloneU8_ok x))
  intro v hv
  simp [alloc.vec.Vec.val, ← hv, hpkeV1, Array.to_slice]

theorem mapM_pure' {α : Type} (l : List α) : List.mapM (m := Result) (fun x => pure x) l = pure l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

theorem mapM_ok {α : Type} (l : List α) : List.mapM (m := Result) (fun x => ok x) l = ok l :=
  mapM_pure' l

theorem borrow_eq {T : Type} : (Shared0T.Insts.CoreBorrowBorrow.borrow : T → Result T) = fun x => ok x := by
  funext x; rfl

theorem intercalate_nil_sep {α : Type} (l : List (List α)) : List.intercalate [] l = l.flatten := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases xs <;> simp_all [List.intercalate_cons_cons]

@[simp] theorem empty_to_slice_val : (Std.Array.empty U8).to_slice.val = [] := by
  simp [Array.to_slice, Std.Array.empty]

theorem vecOfList_spec (l : List U8) (h : l.length ≤ Usize.max) :
    Real.vecOfList l ⦃ v => v.val = l ⦄ := by
  simp [Real.vecOfList, h]

theorem real_concat (values : Slice (Slice U8))
    (h : (values.val.map (·.val)).flatten.length ≤ Usize.max) :
    Real.util.concat values ⦃ v => v.val = (values.val.map (·.val)).flatten ⦄ := by
  unfold Real.util.concat
  simp [core.array.Array.index, alloc.slice.Slice.join,
    Slice.Insts.AllocSliceJoinShared0SliceVec.join,
    borrow_eq, mapM_ok, core.ops.index.IndexSlice, core.slice.index.SliceIndexRangeFullSlice,
    core.slice.index.Slice.index]
  apply spec_bind (list_clone_u8 _)
  intro l hl
  rw [hl]
  simp only [empty_to_slice_val, intercalate_nil_sep]
  exact vecOfList_spec _ h

/-! ## Relations and the shared-primitive hypothesis -/

def refHash : Ref.hpke_kdf.KDF → Shared.Hash
  | .HKDF_SHA256 => .sha256
  | .HKDF_SHA384 => .sha384
  | .HKDF_SHA512 => .sha512

def kdfHash : Real.hpke_rs_crypto.types.KdfAlgorithm → Shared.Hash
  | .HkdfSha256 => .sha256
  | .HkdfSha384 => .sha384
  | .HkdfSha512 => .sha512

/-- The two KDF identifiers name the same algorithm. -/
def KdfRel (a : Ref.hpke_kdf.KDF) (b : Real.hpke_rs_crypto.types.KdfAlgorithm) : Prop :=
  refHash a = kdfHash b

/-- The provider computes HKDF-Extract for the KDF `alg` with the shared model. -/
def ExtractIsShared {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Real.hpke_rs_crypto.types.KdfAlgorithm) : Prop :=
  ∀ salt ikm, inst.kdf_extract alg salt ikm =
    ok (.Ok (Shared.extract (kdfHash alg) salt.val ikm.val))

theorem ref_labeled_extract (alg : Ref.hpke_kdf.KDF) (hS : alg = .HKDF_SHA256)
    (suite salt label ikm : Ref.hacspec_lib.Seq U8)
    (h : hpkeV1.length + suite.b.val.length + label.b.val.length + ikm.b.val.length ≤ Usize.max) :
    Ref.hpke_kdf.LabeledExtract alg suite salt label ikm ⦃ r =>
      r = .Ok { b := Shared.extract (refHash alg) salt.b.val
                    (hpkeV1 ++ suite.b.val ++ label.b.val ++ ikm.b.val) } ⦄ := by
  subst hS
  unfold Ref.hpke_kdf.LabeledExtract
  have hh : Ref.hpke_kdf.hash_for_kdf .HKDF_SHA256 ⦃ ha => ha = .SHA256 ⦄ := by
    simp [Ref.hpke_kdf.hash_for_kdf]
  apply spec_bind hh; intro ha hha
  apply spec_bind ref_version_label; intro s1 hs1
  apply spec_bind (ref_concat _ _ (by simp [hs1]; simp [hpkeV1] at h ⊢; omega)); intro s2 hs2
  apply spec_bind (ref_concat _ _ (by simp [hs2, hs1]; simp [hpkeV1] at h ⊢; omega)); intro s3 hs3
  apply spec_bind (ref_concat _ _ (by simp [hs3, hs2, hs1]; simp [hpkeV1] at h ⊢; omega)); intro s4 hs4
  simp [hacspec_cryptolib.hkdf_extract, hha, hs4, hs3, hs2, hs1, refHash]

theorem real_labeled_extract {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Real.hpke_rs_crypto.types.KdfAlgorithm) (hX : ExtractIsShared inst alg)
    (salt suite : Slice U8) (label : Str) (ikm : Slice U8)
    (h : hpkeV1.length + suite.val.length + label.val.length + ikm.val.length ≤ Usize.max) :
    Real.kdf.labeled_extract inst alg salt suite label ikm ⦃ r =>
      r = .Ok (Shared.extract (kdfHash alg) salt.val
                (hpkeV1 ++ suite.val ++ label.val ++ ikm.val)) ⦄ := by
  unfold Real.kdf.labeled_extract
  simp only [core.str.Str.as_bytes, lift, bind_ok]
  apply spec_bind (real_concat _ (by simp [Array.to_slice, Real.kdf.HPKE_VERSION]; simp [hpkeV1] at h; omega)); intro v hv
  rw [hX]
  simp [hv, Array.to_slice, Real.kdf.HPKE_VERSION, hpkeV1]

theorem ref_be16 (x : U16) :
    Ref.hacspec_lib.U16_to_be_bytes x ⦃ s => s.b.val = x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8) ⦄ := by
  unfold Ref.hacspec_lib.U16_to_be_bytes
  step*
  simp only [b1_post, b_post, i1_post, i2_post, BitVec.toBEBytes]
  rw [BitVec.toLEBytes, BitVec.toLEBytes, BitVec.toLEBytes]
  simp [alloc.vec.Vec.new, alloc.vec.Vec.val, alloc.vec.Vec.from]
  constructor <;> simp [UScalar.cast, i_post1]

def be16 (x : U16) : List U8 := x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)

def nhRef : Ref.hpke_kdf.KDF → Nat
  | .HKDF_SHA256 => 32
  | .HKDF_SHA384 => 48
  | .HKDF_SHA512 => 64

/-- The provider computes HKDF-Expand for the KDF `alg` with the shared model, for a PRK of
the hash length (RFC 5869 requires at least that length, and RFC 9180 passes exactly that).
When the model fails, the provider returns some error. -/
def ExpandIsShared {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Real.hpke_rs_crypto.types.KdfAlgorithm) : Prop :=
  ∀ prk info len, prk.val.length = Shared.hashLen (kdfHash alg) →
    ∃ r, inst.kdf_expand alg prk info len = ok r ∧
      match Shared.expand (kdfHash alg) prk.val info.val len.val with
      | some v => r = .Ok v
      | none => ∃ e, r = .Err e

theorem ref_labeled_expand (alg : Ref.hpke_kdf.KDF) (hS : alg = .HKDF_SHA256)
    (suite prk label info : Ref.hacspec_lib.Seq U8)
    (L : Usize) (hL : L.val ≤ 255 * nhRef alg)
    (h : 2 + hpkeV1.length + suite.b.val.length + label.b.val.length + info.b.val.length ≤ Usize.max) :
    Ref.hpke_kdf.LabeledExpand alg suite prk label info L ⦃ r =>
      r = match Shared.expand (refHash alg) prk.b.val
                (be16 (UScalar.cast .U16 L) ++ hpkeV1 ++ suite.b.val ++ label.b.val ++ info.b.val) L.val with
          | some v => .Ok { b := v }
          | none => .Err .CryptoError ⦄ := by
  subst hS
  unfold Ref.hpke_kdf.LabeledExpand
  have hn : Ref.hpke_kdf.Nh .HKDF_SHA256 ⦃ n => n.val = nhRef .HKDF_SHA256 ⦄ := by
    simp [Ref.hpke_kdf.Nh, nhRef]
  have hh : Ref.hpke_kdf.hash_for_kdf .HKDF_SHA256 ⦃ ha => ha = .SHA256 ⦄ := by
    simp [Ref.hpke_kdf.hash_for_kdf]
  apply spec_bind hn; intro n hn'
  have hm : (255#usize * n) ⦃ m => m.val = 255 * nhRef .HKDF_SHA256 ⦄ := by
    simp only [nhRef] at hn' ⊢
    step*
  apply spec_bind hm; intro m hm'
  have hnot : ¬ (L > m) := by
    simp only [gt_iff_lt, not_lt]; scalar_tac
  simp only [hnot, if_false]
  apply spec_bind hh; intro ha hha
  simp only [lift, bind_ok, Ref.hacspec_lib.U16]
  apply spec_bind (ref_be16 _); intro s0 hs0
  have hb : (be16 (UScalar.cast .U16 L)).length = 2 := by simp [be16]
  rw [← be16] at hs0
  apply spec_bind ref_version_label; intro v hv
  apply spec_bind (ref_concat _ _ (by simp [hs0, hb, hv]; simp [hpkeV1] at h ⊢; omega)); intro s1 hs1
  apply spec_bind (ref_concat _ _ (by simp [hs0, hb, hv, hs1]; simp [hpkeV1] at h ⊢; omega)); intro s2 hs2
  apply spec_bind (ref_concat _ _ (by simp [hs0, hb, hv, hs1, hs2]; simp [hpkeV1] at h ⊢; omega)); intro s3 hs3
  apply spec_bind (ref_concat _ _ (by simp [hs0, hb, hv, hs1, hs2, hs3]; simp [hpkeV1] at h ⊢; omega)); intro s4 hs4
  simp only [hacspec_cryptolib.hkdf_expand, hha, hs4, hs3, hs2, hs1, hv, hs0, bind_ok, List.append_assoc,
    refHash]
  cases Shared.expand .sha256 prk.b.val _ L.val <;> simp

theorem real_labeled_expand {C P E1 E2 : Type} (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Real.hpke_rs_crypto.types.KdfAlgorithm) (hE : ExpandIsShared inst alg)
    (prk suite : Slice U8) (label : Str) (info : Slice U8) (len : Usize)
    (hprk : prk.val.length = Shared.hashLen (kdfHash alg))
    (hlen : len.val ≤ 65535)
    (h : 2 + hpkeV1.length + suite.val.length + label.val.length + info.val.length ≤ Usize.max) :
    Real.kdf.labeled_expand inst alg prk suite label info len ⦃ r =>
      match Shared.expand (kdfHash alg) prk.val
                (be16 (UScalar.cast .U16 len) ++ hpkeV1 ++ suite.val ++ label.val ++ info.val) len.val with
      | some v => r = .Ok v
      | none => ∃ e, r = .Err e ⦄ := by
  unfold Real.kdf.labeled_expand
  simp only [core.convert.IntoFrom.into, bind_ok]
  have hnot : ¬ (len > core.convert.num.FromUsizeU16.from core.num.U16.MAX) := by
    have := core.convert.num.FromUsizeU16.from_val_eq core.num.U16.MAX
    have h2 : (core.num.U16.MAX).val = 65535 := by simp [core.num.U16.MAX, U16.rMax]
    simp only [gt_iff_lt, not_lt]; scalar_tac
  simp only [hnot, if_false]
  have ha := core.num.U16.to_be_bytes.step_spec (UScalar.cast .U16 len)
  simp only [lift, spec_ok] at ha
  simp only [lift, bind_ok, core.str.Str.as_bytes]
  apply spec_bind (real_concat _ (by simp [Array.to_slice, Real.kdf.HPKE_VERSION, ha]; simp [hpkeV1] at h; omega))
  intro v hv
  obtain ⟨r, hr, hm⟩ := hE prk v.deref len hprk
  rw [hr, spec_ok]
  have hv' : v.deref.val = be16 (UScalar.cast .U16 len) ++ hpkeV1 ++ suite.val ++ label.val ++ info.val := by
    simp only [deref_val, hv]
    simp [Array.to_slice, Real.kdf.HPKE_VERSION, ha, be16, hpkeV1]
  rw [hv'] at hm
  exact hm

/-! ## Simulation theorems: real refines reference -/

/-- Output relation: both succeed with the same bytes. -/
def OkRel (r : core.result.Result (alloc.vec.Vec U8) Real.hpke_rs_crypto.error.Error)
    (s : core.result.Result (Ref.hacspec_lib.Seq U8) Ref.hpke_errors.HpkeError) : Prop :=
  ∃ v q, r = .Ok v ∧ s = .Ok q ∧ v.val = q.b.val

theorem labeled_extract_refines {C P E1 E2 : Type}
    (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Ref.hpke_kdf.KDF) (hS : alg = .HKDF_SHA256)
    (ralg : Real.hpke_rs_crypto.types.KdfAlgorithm) (hA : KdfRel alg ralg)
    (hX : ExtractIsShared inst ralg)
    (salt suite : Slice U8) (label : Str) (ikm : Slice U8)
    (rsalt rsuite rlabel rikm : Ref.hacspec_lib.Seq U8)
    (h1 : rsalt.b.val = salt.val) (h2 : rsuite.b.val = suite.val)
    (h3 : rlabel.b.val = label.val) (h4 : rikm.b.val = ikm.val)
    (h : 7 + suite.val.length + label.val.length + ikm.val.length ≤ Usize.max) :
    Real.kdf.labeled_extract inst ralg salt suite label ikm ⦃ r =>
      Ref.hpke_kdf.LabeledExtract alg rsuite rsalt rlabel rikm ⦃ s => OkRel r s ⦄ ⦄ := by
  apply spec_mono (real_labeled_extract inst ralg hX salt suite label ikm (by simpa [hpkeV1] using h))
  intro r hr
  apply spec_mono (ref_labeled_extract alg hS rsuite rsalt rlabel rikm (by simp [hpkeV1, h2, h3, h4]; omega))
  intro s hs
  refine ⟨_, _, hr, hs, ?_⟩
  simp only [KdfRel] at hA
  simp only [h1, h2, h3, h4, hA]

/-- The real code passes the salt `[0x00]` where RFC 9180 and the reference pass the
empty salt. The two agree because HMAC zero-pads short keys. -/
theorem labeled_extract_refines_zero_salt {C P E1 E2 : Type}
    (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Ref.hpke_kdf.KDF) (hS : alg = .HKDF_SHA256)
    (ralg : Real.hpke_rs_crypto.types.KdfAlgorithm) (hA : KdfRel alg ralg)
    (hX : ExtractIsShared inst ralg)
    (salt suite : Slice U8) (label : Str) (ikm : Slice U8)
    (rsalt rsuite rlabel rikm : Ref.hacspec_lib.Seq U8)
    (h1 : salt.val = [0#u8]) (h1' : rsalt.b.val = []) (h2 : rsuite.b.val = suite.val)
    (h3 : rlabel.b.val = label.val) (h4 : rikm.b.val = ikm.val)
    (h : 7 + suite.val.length + label.val.length + ikm.val.length ≤ Usize.max) :
    Real.kdf.labeled_extract inst ralg salt suite label ikm ⦃ r =>
      Ref.hpke_kdf.LabeledExtract alg rsuite rsalt rlabel rikm ⦃ s => OkRel r s ⦄ ⦄ := by
  apply spec_mono (real_labeled_extract inst ralg hX salt suite label ikm (by simpa [hpkeV1] using h))
  intro r hr
  apply spec_mono (ref_labeled_extract alg hS rsuite rsalt rlabel rikm (by simp [hpkeV1, h2, h3, h4]; omega))
  intro s hs
  refine ⟨_, _, hr, hs, ?_⟩
  simp only [KdfRel] at hA
  simp only [h1, h1', h2, h3, h4, hA, Shared.extract_salt_zero]

theorem labeled_expand_refines {C P E1 E2 : Type}
    (inst : Real.hpke_rs_crypto.HpkeCrypto C P E1 E2)
    (alg : Ref.hpke_kdf.KDF) (hS : alg = .HKDF_SHA256)
    (ralg : Real.hpke_rs_crypto.types.KdfAlgorithm) (hA : KdfRel alg ralg)
    (hE : ExpandIsShared inst ralg)
    (prk suite : Slice U8) (label : Str) (info : Slice U8) (len : Usize)
    (rprk rsuite rlabel rinfo : Ref.hacspec_lib.Seq U8)
    (h1 : rprk.b.val = prk.val) (h2 : rsuite.b.val = suite.val)
    (h3 : rlabel.b.val = label.val) (h4 : rinfo.b.val = info.val)
    (hprk : prk.val.length = Shared.hashLen (kdfHash ralg))
    (hL : len.val ≤ 255 * nhRef alg)
    (h : 9 + suite.val.length + label.val.length + info.val.length ≤ Usize.max) :
    Real.kdf.labeled_expand inst ralg prk suite label info len ⦃ r =>
      Ref.hpke_kdf.LabeledExpand alg rsuite rprk rlabel rinfo len ⦃ s => OkRel r s ⦄ ⦄ := by
  have hL' : len.val ≤ 65535 := by
    have : nhRef alg ≤ 64 := by cases alg <;> simp [nhRef]
    omega
  apply spec_mono (real_labeled_expand inst ralg hE prk suite label info len hprk hL'
    (by simpa [hpkeV1] using h))
  intro r hr
  apply spec_mono (ref_labeled_expand alg hS rsuite rprk rlabel rinfo len hL
    (by simp [hpkeV1, h2, h3, h4]; omega))
  intro s hs
  simp only [KdfRel] at hA
  subst hS
  simp only [h1, h2, h3, h4, hA] at hs
  have hk : kdfHash ralg = .sha256 := by rw [← hA]; rfl
  rw [hk] at hr hs
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp
    (Shared.expand_ne_none .sha256 prk.val
      (be16 (UScalar.cast .U16 len) ++ hpkeV1 ++ suite.val ++ label.val ++ info.val) len.val
      (by simpa [nhRef, Shared.hashLen] using hL))
  rw [hv] at hr hs
  exact ⟨v, { b := v }, hr, hs, rfl⟩
end Sim
