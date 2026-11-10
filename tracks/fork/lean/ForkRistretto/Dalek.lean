import ForkRistretto.ScalarMul
import Specs.Ristretto
import Specs.Scalar

/-! # curve25519-dalek 5.0.0 against the reference, through the fork's specs

For each of the four builds of the fork's translation (`x86_64-tables`, `i686-tables`,
`x86_64-no-tables`, `i686-no-tables`), with the limb bound `n` of the build (52 on x86_64, 26
on i686):

- `decompress_refines`: for every 32-byte input, `CompressedRistretto::decompress` returns
  a result `r`. The reference `decode` returns a result `q` with `DecRel q (r.map toPoint)`: it
  rejects the input exactly when dalek does, and otherwise returns `(x, y, 1, x y)` for the
  point `(x, y)` that the dalek result represents. A returned point is on the curve, even, and
  has limbs below `2 ^ n`.
- `compress_refines`: for a point on the curve with limbs below `2 ^ n`,
  `RistrettoPoint::compress` returns the bytes of the reference `encode` of the point's
  coordinates.
- `mul_refines`: for a point `P` as above and a scalar `k` below `2 ^ 255`,
  `Mul<&Scalar> for &RistrettoPoint` returns a point `r` on the curve with limbs below `2 ^ n`,
  even if `P` is even. If moreover `k < l` or `l • P = 0`, the reference `point_mul s` on the
  coordinates of `P`, with `s = k` in `ZMod l`, returns a representative of `r`.
- `mul_compress_refines`: for an even point `P` as above, a scalar `k` below `2 ^ 255`, and any
  reference representative `Q` of `P`,
  `compress` of the dalek product returns the bytes of the reference
  `encode (point_mul s Q)`. It needs no premise `k < l`: the two products differ by 4-torsion,
  which the encoding does not see.
- `decompress_mul_compress_refines`: decode, multiply and encode. If `decompress` rejects the
  input, the reference `decode` returns the error `20`. Otherwise `decode` returns `Ok q`, and
  `compress` of the dalek product returns the bytes of the reference `encode (point_mul s q)`.
- `from_bytes_decompress_mul_compress_refines`: the same, with the scalar made by
  `Scalar::from_bytes_mod_order` from 32 bytes `sb`, and the reference scalar `s = sb` in
  `ZMod l`. It has no premise.

The fork's `mul` reads the scalar as the integer of its 32 bytes, `k.asNat`, not reduced mod
`l`, with the premise `k.asNat < 2 ^ 255`. The reference reads it as an element `s` of
`ZMod l`. The theorems link the two with `(k.asNat : ZMod l) = s`.

The section `Compose` proves each theorem once, for any build, from the fork's specs given as
hypotheses. Each build then applies these lemmas to its own specs. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519

namespace ForkRistretto

/-- If `m ⦃ x => P x ⦄`, then `m = ok x` for some `x` with `P x`. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ x => P x ⦄) :
    ∃ x, m = ok x ∧ P x := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact ((spec_vis i k).mp h).elim
  | div => exact (spec_div.mp h).elim

/-- The reference coordinates of extended coordinates of the fork. -/
def extRef (E : edwards.Extended) : RefPt :=
  (toF.symm E.X, toF.symm E.Y, toF.symm E.Z, toF.symm E.T)

/-- Extended coordinates on the curve represent their point. -/
theorem rep_extRef {E : edwards.Extended} (h : E.OnCurve) : Rep (extRef E) E.toPoint := by
  obtain ⟨hZ, hT, _⟩ := h
  simp only [Rep, extRef, RingEquiv.apply_symm_apply]
  exact ⟨hZ, hT, TwistedEdwardsModel.Extended.toPoint_x ⟨hZ, hT, ‹_›⟩,
    TwistedEdwardsModel.Extended.toPoint_y ⟨hZ, hT, ‹_›⟩⟩

/-- The reference coordinates `(x, y, 1, x y)` represent `(x, y)`. -/
theorem rep_refOf (P : edwards.Point) : Rep (refOf P) P := by
  simp only [Rep, refOf, RingEquiv.apply_symm_apply, map_one, div_one, one_mul]
  exact ⟨one_ne_zero, trivial, trivial, trivial⟩

/-- A result of the reference `decode` that matches `some P` is `Ok (refOf P)`. -/
theorem decRel_some {q : core.result.Result RefPt U8} {P : edwards.Point}
    (h : DecRel q (some P)) : q = .Ok (refOf P) := by
  cases q with
  | Ok q => exact congrArg _ h
  | Err e => exact h.elim

/-- A result of the reference `decode` that matches `none` is the error `20`. -/
theorem decRel_none {q : core.result.Result RefPt U8} (h : DecRel q none) : q = .Err 20#u8 := by
  cases q with
  | Ok q => exact h.elim
  | Err e => exact congrArg _ h

/-- `decode` and `decodeRep` composed with a decompress spec. -/
theorem decode_of_decodeRep {β : Type} (bytes : Array U8 32#usize) (r : Option β)
    (toPoint : β → edwards.Point) (h : r.map toPoint = Ristretto.decodeRep (bytes.asNat 8)) :
    ∃ q, ristretto_ref.decode bytes = ok q ∧ DecRel q (r.map toPoint) := by
  rw [h]
  exact exists_ok_of_spec (decode_spec bytes)

/-- `encode` and `encodeRep` composed with a compress spec. -/
theorem encode_of_encodeRep (c : Array U8 32#usize) (q : RefPt) (P : edwards.Point)
    (hq : Rep q P) (h : c.asNat 8 = Ristretto.encodeRep P) :
    ristretto_ref.encode q = ok c := by
  obtain ⟨c', hc', hv⟩ := exists_ok_of_spec (encode_spec _ _ hq)
  rw [hc', Array.eq_of_asNat_eq (hv.trans h.symm)]

/-- `l < 2 ^ 255`. -/
theorem L_lt_two_pow : L < 2 ^ 255 := by
  rw [← scalar_l_eq]
  norm_num [scalar.l]

/-! ## The compositions, for any build

`Pt` is the point type of a build, `toPoint` its affine point, `ext` its coordinates in the
reference, `OnC` and `Lim` its predicates `OnCurve` and `LimbsLt n`. The hypotheses are the
shapes of the fork's specs: `hdec` of `decompress`, `hcomp` of `compress`, `hmul` of `mul`, and
`hrep` says that the coordinates of a point on the curve represent it. -/

section Compose

open Curve25519Dalek

variable {Pt : Type} {toPoint : Pt → edwards.Point} {ext : Pt → RefPt} {OnC Lim : Pt → Prop}

theorem decompress_refines_of {dec : ristretto.CompressedRistretto → Result (Option Pt)}
    (hdec : ∀ b, dec b ⦃ r => r.map toPoint = Ristretto.decodeRep b.asNat ∧
      ∀ q, r = some q → OnC q ∧ Even (toPoint q) ∧ Lim q ⦄)
    (bytes : ristretto.CompressedRistretto) :
    dec bytes ⦃ r => (∃ q, ristretto_ref.decode bytes = ok q ∧ DecRel q (r.map toPoint)) ∧
      ∀ P, r = some P → OnC P ∧ Even (toPoint P) ∧ Lim P ⦄ :=
  spec_mono (hdec bytes) fun r h =>
    ⟨decode_of_decodeRep bytes r _ (by rw [h.1, ristretto.CompressedRistretto.asNat_def]), h.2⟩

theorem compress_refines_of {comp : Pt → Result ristretto.CompressedRistretto}
    (hrep : ∀ P, OnC P → Rep (ext P) (toPoint P))
    (hcomp : ∀ P, Lim P → OnC P → comp P ⦃ c => c.asNat = Ristretto.encodeRep (toPoint P) ⦄)
    (P : Pt) (hP : Lim P) (hon : OnC P) :
    comp P ⦃ c => ristretto_ref.encode (ext P) = ok c ⦄ :=
  spec_mono (hcomp P hP hon) fun c h =>
    encode_of_encodeRep c _ _ (hrep P hon)
      (by rw [← ristretto.CompressedRistretto.asNat_def]; exact h)

theorem mul_refines_of {mul : Pt → Curve25519Dalek.scalar.Scalar → Result Pt}
    (hrep : ∀ P, OnC P → Rep (ext P) (toPoint P))
    (hmul : ∀ P k, Lim P → OnC P → k.asNat < 2 ^ 255 →
      mul P k ⦃ r => OnC r ∧ toPoint r = k.asNat • toPoint P ∧ Lim r ⦄)
    (P : Pt) (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : Lim P) (hon : OnC P) (hk : k.asNat < 2 ^ 255) :
    mul P k ⦃ r => OnC r ∧ Lim r ∧ (Even (toPoint P) → Even (toPoint r)) ∧
      (k.asNat < L ∨ L • toPoint P = 0 →
        ∃ q, ristretto_ref.edwards.point_mul s (ext P) = ok q ∧ Rep q (toPoint r)) ⦄ :=
  spec_mono (hmul P k hP hon hk) fun r h => by
    refine ⟨h.1, h.2.2, fun hev => h.2.1 ▸ even_nsmul hev _, fun hkL => ?_⟩
    obtain ⟨q, hq, hrep'⟩ :=
      exists_ok_of_spec (point_mul_spec_of k.asNat s hs _ _ (hrep P hon) hkL)
    exact ⟨q, hq, h.2.1 ▸ hrep'⟩

theorem mul_compress_refines_of {mul : Pt → Curve25519Dalek.scalar.Scalar → Result Pt}
    {comp : Pt → Result ristretto.CompressedRistretto}
    (hmul : ∀ P k, Lim P → OnC P → k.asNat < 2 ^ 255 →
      mul P k ⦃ r => OnC r ∧ toPoint r = k.asNat • toPoint P ∧ Lim r ⦄)
    (hcomp : ∀ P, Lim P → OnC P → comp P ⦃ c => c.asNat = Ristretto.encodeRep (toPoint P) ⦄)
    (P : Pt) (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : Lim P) (hon : OnC P) (hev : Even (toPoint P)) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q (toPoint P)) :
    mul P k ⦃ r => comp r ⦃ c =>
      ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  spec_mono (hmul P k hP hon hk) fun r ⟨hon', hr, hl⟩ =>
    spec_mono (hcomp r hl hon') fun c hc => by
      obtain ⟨q, hq, henc⟩ := exists_ok_of_spec (point_mul_encode_spec k.asNat s hs Q _ hQ hev)
      obtain ⟨c', hc', hv⟩ := exists_ok_of_spec henc
      refine ⟨q, hq, ?_⟩
      rw [hc', Array.eq_of_asNat_eq (hv.trans (hr ▸ hc.symm))]

theorem decompress_mul_compress_refines_of
    {dec : ristretto.CompressedRistretto → Result (Option Pt)}
    {mul : Pt → Curve25519Dalek.scalar.Scalar → Result Pt}
    {comp : Pt → Result ristretto.CompressedRistretto}
    (hdec : ∀ b, dec b ⦃ r => r.map toPoint = Ristretto.decodeRep b.asNat ∧
      ∀ q, r = some q → OnC q ∧ Even (toPoint q) ∧ Lim q ⦄)
    (hmul : ∀ P k, Lim P → OnC P → k.asNat < 2 ^ 255 →
      mul P k ⦃ r => OnC r ∧ toPoint r = k.asNat • toPoint P ∧ Lim r ⦄)
    (hcomp : ∀ P, Lim P → OnC P → comp P ⦃ c => c.asNat = Ristretto.encodeRep (toPoint P) ⦄)
    (bytes : ristretto.CompressedRistretto) (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hk : k.asNat < 2 ^ 255) :
    dec bytes ⦃ r => (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
      ∀ P, r = some P → mul P k ⦃ r' => comp r' ⦃ c =>
        ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
          ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  spec_mono (decompress_refines_of hdec bytes) fun r ⟨⟨dq, hdq, hrel⟩, hpt⟩ => by
    refine ⟨fun hn => ?_, fun P hr => ?_⟩
    · subst hn
      rw [hdq, decRel_none hrel]
    · obtain ⟨hon, hev, hl⟩ := hpt P hr
      subst hr
      have hdq' := decRel_some hrel
      subst hdq'
      exact spec_mono (mul_compress_refines_of hmul hcomp P k s hs hl hon hev hk _ (rep_refOf _))
        fun r' h' => spec_mono h' fun c ⟨q', hq', he⟩ => ⟨_, q', hdq, hq', he⟩

theorem from_bytes_decompress_mul_compress_refines_of
    {dec : ristretto.CompressedRistretto → Result (Option Pt)}
    {mul : Pt → Curve25519Dalek.scalar.Scalar → Result Pt}
    {comp : Pt → Result ristretto.CompressedRistretto}
    (hdec : ∀ b, dec b ⦃ r => r.map toPoint = Ristretto.decodeRep b.asNat ∧
      ∀ q, r = some q → OnC q ∧ Even (toPoint q) ∧ Lim q ⦄)
    (hmul : ∀ P k, Lim P → OnC P → k.asNat < 2 ^ 255 →
      mul P k ⦃ r => OnC r ∧ toPoint r = k.asNat • toPoint P ∧ Lim r ⦄)
    (hcomp : ∀ P, Lim P → OnC P → comp P ⦃ c => c.asNat = Ristretto.encodeRep (toPoint P) ⦄)
    (bytes : ristretto.CompressedRistretto) (sb : Array U8 32#usize) (s : _root_.scalar.Scalar)
    (hs : ((sb.asNat 8 : ℕ) : ZMod _root_.scalar.l) = s) :
    Curve25519Dalek.scalar.Scalar.from_bytes_mod_order sb ⦃ k =>
      dec bytes ⦃ r => (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
        ∀ P, r = some P → mul P k ⦃ r' => comp r' ⦃ c =>
          ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
            ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ ⦄ :=
  spec_mono (Curve25519Dalek.scalar.Scalar.from_bytes_mod_order_spec sb) fun k hk => by
    have hL0 : 0 < L := by rw [← scalar_l_eq]; norm_num [scalar.l]
    refine decompress_mul_compress_refines_of hdec hmul hcomp bytes k s ?_ ?_
    · rw [hk, ← scalar_l_eq, ZMod.natCast_mod]
      exact hs
    · rw [hk]
      exact lt_trans (Nat.mod_lt _ hL0) L_lt_two_pow

end Compose

/-! ## Build `x86_64-tables` -/

namespace «x86_64-tables»

open Curve25519Dalek

/-- The coordinates of a point on the curve represent `toPoint`. -/
theorem rep_toExtended (P : edwards.EdwardsPoint.«x86_64-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«x86_64-tables».toPoint_def]
  exact rep_extRef hon

/-- `decompress bytes` returns `r`, and the reference `decode bytes` returns `q` with
`DecRel q (r.map toPoint)`. A returned point is on the curve, even, and has limbs `< 2 ^ 52`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«x86_64-tables» bytes ⦃ r =>
      (∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«x86_64-tables».toPoint)) ∧
      ∀ P, r = some P → P.OnCurve ∧ Even P.toPoint ∧ P.LimbsLt 52 ⦄ :=
  decompress_refines_of ristretto.CompressedRistretto.«x86_64-tables».decompress_spec bytes

/-- If `P` is on the curve with limbs `< 2 ^ 52`, `compress P` returns the bytes of the
reference `encode` of the coordinates of `P`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«x86_64-tables») (hP : P.LimbsLt 52)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointx86_64-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  compress_refines_of rep_toExtended ristretto.«RistrettoPointx86_64-tables».compress_spec P hP hon

/-- If `P` is on the curve with limbs `< 2 ^ 52` and `k.asNat < 2 ^ 255`, then `P * k` returns a
point `r` on the curve with limbs `< 2 ^ 52`, and `r` is even if `P` is even. If moreover
`k.asNat < l` or `l • P = 0`, the reference `point_mul s` on the coordinates of `P`, with
`s = k.asNat` in `ZMod l`, returns a representative of `r`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«x86_64-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255) :
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
      ⦃ r => r.OnCurve ∧ r.LimbsLt 52 ∧ (Even P.toPoint → Even r.toPoint) ∧
        (k.asNat < L ∨ L • P.toPoint = 0 →
          ∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
            Rep q r.toPoint) ⦄ :=
  mul_refines_of rep_toExtended
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec
    P k s hs hP hon hk

/-- If `P` is even, on the curve with limbs `< 2 ^ 52`, `k.asNat < 2 ^ 255`, and `Q` is any
reference representative of `P`, then `compress (P * k)` returns the bytes of the reference
`encode (point_mul s Q)`, with `s = k.asNat` in `ZMod l`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«x86_64-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointx86_64-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  mul_compress_refines_of
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec
    ristretto.«RistrettoPointx86_64-tables».compress_spec P k s hs hP hon hev hk Q hQ

/-- Decode, multiply and encode, with `s = k.asNat` in `ZMod l` and `k.asNat < 2 ^ 255`. If
`decompress bytes` returns `none`, the reference `decode bytes` returns the error `20`. If it
returns `P`, `decode bytes` returns `Ok q`, and `compress (P * k)` returns the bytes of the
reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«x86_64-tables» bytes ⦃ r =>
      (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
      ∀ P, r = some P →
        «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
          ⦃ r' => ristretto.«RistrettoPointx86_64-tables».compress r' ⦃ c =>
            ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
              ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  decompress_mul_compress_refines_of ristretto.CompressedRistretto.«x86_64-tables».decompress_spec
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec
    ristretto.«RistrettoPointx86_64-tables».compress_spec bytes k s hs hk

/-- Decode, multiply and encode, with the scalar `k = Scalar::from_bytes_mod_order sb` and the
reference scalar `s = sb.asNat 8` in `ZMod l`. If `decompress bytes` returns `none`, the
reference `decode bytes` returns the error `20`. If it returns `P`, `decode bytes` returns
`Ok q`, and `compress (P * k)` returns the bytes of the reference `encode (point_mul s q)`. -/
theorem from_bytes_decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (sb : Array U8 32#usize) (s : _root_.scalar.Scalar)
    (hs : ((sb.asNat 8 : ℕ) : ZMod _root_.scalar.l) = s) :
    Curve25519Dalek.scalar.Scalar.from_bytes_mod_order sb ⦃ k =>
      ristretto.CompressedRistretto.decompress.«x86_64-tables» bytes ⦃ r =>
        (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
        ∀ P, r = some P →
          «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
            ⦃ r' => ristretto.«RistrettoPointx86_64-tables».compress r' ⦃ c =>
              ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
                ristretto_ref.edwards.point_mul s q = ok q' ∧
                ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ ⦄ :=
  from_bytes_decompress_mul_compress_refines_of
    ristretto.CompressedRistretto.«x86_64-tables».decompress_spec
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec
    ristretto.«RistrettoPointx86_64-tables».compress_spec bytes sb s hs

end «x86_64-tables»

/-! ## Build `i686-tables` -/

namespace «i686-tables»

open Curve25519Dalek

/-- The coordinates of a point on the curve represent `toPoint`. -/
theorem rep_toExtended (P : edwards.EdwardsPoint.«i686-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«i686-tables».toPoint_def]
  exact rep_extRef hon

/-- `decompress bytes` returns `r`, and the reference `decode bytes` returns `q` with
`DecRel q (r.map toPoint)`. A returned point is on the curve, even, and has limbs `< 2 ^ 26`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«i686-tables» bytes ⦃ r =>
      (∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«i686-tables».toPoint)) ∧
      ∀ P, r = some P → P.OnCurve ∧ Even P.toPoint ∧ P.LimbsLt 26 ⦄ :=
  decompress_refines_of ristretto.CompressedRistretto.«i686-tables».decompress_spec bytes

/-- If `P` is on the curve with limbs `< 2 ^ 26`, `compress P` returns the bytes of the
reference `encode` of the coordinates of `P`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«i686-tables») (hP : P.LimbsLt 26)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointi686-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  compress_refines_of rep_toExtended ristretto.«RistrettoPointi686-tables».compress_spec P hP hon

/-- If `P` is on the curve with limbs `< 2 ^ 26` and `k.asNat < 2 ^ 255`, then `P * k` returns a
point `r` on the curve with limbs `< 2 ^ 26`, and `r` is even if `P` is even. If moreover
`k.asNat < l` or `l • P = 0`, the reference `point_mul s` on the coordinates of `P`, with
`s = k.asNat` in `ZMod l`, returns a representative of `r`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«i686-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255) :
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
      ⦃ r => r.OnCurve ∧ r.LimbsLt 26 ∧ (Even P.toPoint → Even r.toPoint) ∧
        (k.asNat < L ∨ L • P.toPoint = 0 →
          ∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
            Rep q r.toPoint) ⦄ :=
  mul_refines_of rep_toExtended
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul_spec
    P k s hs hP hon hk

/-- If `P` is even, on the curve with limbs `< 2 ^ 26`, `k.asNat < 2 ^ 255`, and `Q` is any
reference representative of `P`, then `compress (P * k)` returns the bytes of the reference
`encode (point_mul s Q)`, with `s = k.asNat` in `ZMod l`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«i686-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointi686-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  mul_compress_refines_of
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul_spec
    ristretto.«RistrettoPointi686-tables».compress_spec P k s hs hP hon hev hk Q hQ

/-- Decode, multiply and encode, with `s = k.asNat` in `ZMod l` and `k.asNat < 2 ^ 255`. If
`decompress bytes` returns `none`, the reference `decode bytes` returns the error `20`. If it
returns `P`, `decode bytes` returns `Ok q`, and `compress (P * k)` returns the bytes of the
reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«i686-tables» bytes ⦃ r =>
      (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
      ∀ P, r = some P →
        «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
          ⦃ r' => ristretto.«RistrettoPointi686-tables».compress r' ⦃ c =>
            ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
              ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  decompress_mul_compress_refines_of ristretto.CompressedRistretto.«i686-tables».decompress_spec
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul_spec
    ristretto.«RistrettoPointi686-tables».compress_spec bytes k s hs hk

/-- Decode, multiply and encode, with the scalar `k = Scalar::from_bytes_mod_order sb` and the
reference scalar `s = sb.asNat 8` in `ZMod l`. If `decompress bytes` returns `none`, the
reference `decode bytes` returns the error `20`. If it returns `P`, `decode bytes` returns
`Ok q`, and `compress (P * k)` returns the bytes of the reference `encode (point_mul s q)`. -/
theorem from_bytes_decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (sb : Array U8 32#usize) (s : _root_.scalar.Scalar)
    (hs : ((sb.asNat 8 : ℕ) : ZMod _root_.scalar.l) = s) :
    Curve25519Dalek.scalar.Scalar.from_bytes_mod_order sb ⦃ k =>
      ristretto.CompressedRistretto.decompress.«i686-tables» bytes ⦃ r =>
        (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
        ∀ P, r = some P →
          «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
            ⦃ r' => ristretto.«RistrettoPointi686-tables».compress r' ⦃ c =>
              ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
                ristretto_ref.edwards.point_mul s q = ok q' ∧
                ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ ⦄ :=
  from_bytes_decompress_mul_compress_refines_of
    ristretto.CompressedRistretto.«i686-tables».decompress_spec
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul_spec
    ristretto.«RistrettoPointi686-tables».compress_spec bytes sb s hs

end «i686-tables»

/-! ## Build `x86_64-no-tables` -/

namespace «x86_64-no-tables»

open Curve25519Dalek

/-- The coordinates of a point on the curve represent `toPoint`. -/
theorem rep_toExtended (P : edwards.EdwardsPoint.«x86_64-no-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def]
  exact rep_extRef hon

/-- `decompress bytes` returns `r`, and the reference `decode bytes` returns `q` with
`DecRel q (r.map toPoint)`. A returned point is on the curve, even, and has limbs `< 2 ^ 52`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«x86_64-no-tables» bytes ⦃ r =>
      (∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint)) ∧
      ∀ P, r = some P → P.OnCurve ∧ Even P.toPoint ∧ P.LimbsLt 52 ⦄ :=
  decompress_refines_of ristretto.CompressedRistretto.«x86_64-no-tables».decompress_spec bytes

/-- If `P` is on the curve with limbs `< 2 ^ 52`, `compress P` returns the bytes of the
reference `encode` of the coordinates of `P`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«x86_64-no-tables») (hP : P.LimbsLt 52)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointx86_64-no-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  compress_refines_of rep_toExtended ristretto.«RistrettoPointx86_64-no-tables».compress_spec P hP hon

/-- If `P` is on the curve with limbs `< 2 ^ 52` and `k.asNat < 2 ^ 255`, then `P * k` returns a
point `r` on the curve with limbs `< 2 ^ 52`, and `r` is even if `P` is even. If moreover
`k.asNat < l` or `l • P = 0`, the reference `point_mul s` on the coordinates of `P`, with
`s = k.asNat` in `ZMod l`, returns a representative of `r`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«x86_64-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255) :
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
      ⦃ r => r.OnCurve ∧ r.LimbsLt 52 ∧ (Even P.toPoint → Even r.toPoint) ∧
        (k.asNat < L ∨ L • P.toPoint = 0 →
          ∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
            Rep q r.toPoint) ⦄ :=
  mul_refines_of rep_toExtended
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul_spec
    P k s hs hP hon hk

/-- If `P` is even, on the curve with limbs `< 2 ^ 52`, `k.asNat < 2 ^ 255`, and `Q` is any
reference representative of `P`, then `compress (P * k)` returns the bytes of the reference
`encode (point_mul s Q)`, with `s = k.asNat` in `ZMod l`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«x86_64-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointx86_64-no-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  mul_compress_refines_of
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul_spec
    ristretto.«RistrettoPointx86_64-no-tables».compress_spec P k s hs hP hon hev hk Q hQ

/-- Decode, multiply and encode, with `s = k.asNat` in `ZMod l` and `k.asNat < 2 ^ 255`. If
`decompress bytes` returns `none`, the reference `decode bytes` returns the error `20`. If it
returns `P`, `decode bytes` returns `Ok q`, and `compress (P * k)` returns the bytes of the
reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«x86_64-no-tables» bytes ⦃ r =>
      (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
      ∀ P, r = some P →
        «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
          ⦃ r' => ristretto.«RistrettoPointx86_64-no-tables».compress r' ⦃ c =>
            ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
              ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  decompress_mul_compress_refines_of ristretto.CompressedRistretto.«x86_64-no-tables».decompress_spec
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul_spec
    ristretto.«RistrettoPointx86_64-no-tables».compress_spec bytes k s hs hk

/-- Decode, multiply and encode, with the scalar `k = Scalar::from_bytes_mod_order sb` and the
reference scalar `s = sb.asNat 8` in `ZMod l`. If `decompress bytes` returns `none`, the
reference `decode bytes` returns the error `20`. If it returns `P`, `decode bytes` returns
`Ok q`, and `compress (P * k)` returns the bytes of the reference `encode (point_mul s q)`. -/
theorem from_bytes_decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (sb : Array U8 32#usize) (s : _root_.scalar.Scalar)
    (hs : ((sb.asNat 8 : ℕ) : ZMod _root_.scalar.l) = s) :
    Curve25519Dalek.scalar.Scalar.from_bytes_mod_order sb ⦃ k =>
      ristretto.CompressedRistretto.decompress.«x86_64-no-tables» bytes ⦃ r =>
        (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
        ∀ P, r = some P →
          «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
            ⦃ r' => ristretto.«RistrettoPointx86_64-no-tables».compress r' ⦃ c =>
              ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
                ristretto_ref.edwards.point_mul s q = ok q' ∧
                ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ ⦄ :=
  from_bytes_decompress_mul_compress_refines_of
    ristretto.CompressedRistretto.«x86_64-no-tables».decompress_spec
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul_spec
    ristretto.«RistrettoPointx86_64-no-tables».compress_spec bytes sb s hs

end «x86_64-no-tables»

/-! ## Build `i686-no-tables` -/

namespace «i686-no-tables»

open Curve25519Dalek

/-- The coordinates of a point on the curve represent `toPoint`. -/
theorem rep_toExtended (P : edwards.EdwardsPoint.«i686-no-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«i686-no-tables».toPoint_def]
  exact rep_extRef hon

/-- `decompress bytes` returns `r`, and the reference `decode bytes` returns `q` with
`DecRel q (r.map toPoint)`. A returned point is on the curve, even, and has limbs `< 2 ^ 26`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«i686-no-tables» bytes ⦃ r =>
      (∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«i686-no-tables».toPoint)) ∧
      ∀ P, r = some P → P.OnCurve ∧ Even P.toPoint ∧ P.LimbsLt 26 ⦄ :=
  decompress_refines_of ristretto.CompressedRistretto.«i686-no-tables».decompress_spec bytes

/-- If `P` is on the curve with limbs `< 2 ^ 26`, `compress P` returns the bytes of the
reference `encode` of the coordinates of `P`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«i686-no-tables») (hP : P.LimbsLt 26)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointi686-no-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  compress_refines_of rep_toExtended ristretto.«RistrettoPointi686-no-tables».compress_spec P hP hon

/-- If `P` is on the curve with limbs `< 2 ^ 26` and `k.asNat < 2 ^ 255`, then `P * k` returns a
point `r` on the curve with limbs `< 2 ^ 26`, and `r` is even if `P` is even. If moreover
`k.asNat < l` or `l • P = 0`, the reference `point_mul s` on the coordinates of `P`, with
`s = k.asNat` in `ZMod l`, returns a representative of `r`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«i686-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255) :
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
      ⦃ r => r.OnCurve ∧ r.LimbsLt 26 ∧ (Even P.toPoint → Even r.toPoint) ∧
        (k.asNat < L ∨ L • P.toPoint = 0 →
          ∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
            Rep q r.toPoint) ⦄ :=
  mul_refines_of rep_toExtended
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul_spec
    P k s hs hP hon hk

/-- If `P` is even, on the curve with limbs `< 2 ^ 26`, `k.asNat < 2 ^ 255`, and `Q` is any
reference representative of `P`, then `compress (P * k)` returns the bytes of the reference
`encode (point_mul s Q)`, with `s = k.asNat` in `ZMod l`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«i686-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointi686-no-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  mul_compress_refines_of
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul_spec
    ristretto.«RistrettoPointi686-no-tables».compress_spec P k s hs hP hon hev hk Q hQ

/-- Decode, multiply and encode, with `s = k.asNat` in `ZMod l` and `k.asNat < 2 ^ 255`. If
`decompress bytes` returns `none`, the reference `decode bytes` returns the error `20`. If it
returns `P`, `decode bytes` returns `Ok q`, and `compress (P * k)` returns the bytes of the
reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«i686-no-tables» bytes ⦃ r =>
      (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
      ∀ P, r = some P →
        «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
          ⦃ r' => ristretto.«RistrettoPointi686-no-tables».compress r' ⦃ c =>
            ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
              ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  decompress_mul_compress_refines_of ristretto.CompressedRistretto.«i686-no-tables».decompress_spec
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul_spec
    ristretto.«RistrettoPointi686-no-tables».compress_spec bytes k s hs hk

/-- Decode, multiply and encode, with the scalar `k = Scalar::from_bytes_mod_order sb` and the
reference scalar `s = sb.asNat 8` in `ZMod l`. If `decompress bytes` returns `none`, the
reference `decode bytes` returns the error `20`. If it returns `P`, `decode bytes` returns
`Ok q`, and `compress (P * k)` returns the bytes of the reference `encode (point_mul s q)`. -/
theorem from_bytes_decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (sb : Array U8 32#usize) (s : _root_.scalar.Scalar)
    (hs : ((sb.asNat 8 : ℕ) : ZMod _root_.scalar.l) = s) :
    Curve25519Dalek.scalar.Scalar.from_bytes_mod_order sb ⦃ k =>
      ristretto.CompressedRistretto.decompress.«i686-no-tables» bytes ⦃ r =>
        (r = none → ristretto_ref.decode bytes = ok (.Err 20#u8)) ∧
        ∀ P, r = some P →
          «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
            ⦃ r' => ristretto.«RistrettoPointi686-no-tables».compress r' ⦃ c =>
              ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
                ristretto_ref.edwards.point_mul s q = ok q' ∧
                ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ ⦄ :=
  from_bytes_decompress_mul_compress_refines_of
    ristretto.CompressedRistretto.«i686-no-tables».decompress_spec
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul_spec
    ristretto.«RistrettoPointi686-no-tables».compress_spec bytes sb s hs

end «i686-no-tables»

end ForkRistretto
