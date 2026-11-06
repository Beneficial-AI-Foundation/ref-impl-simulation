import ForkRistretto.ScalarMul
import Specs.Ristretto

/-! # curve25519-dalek 5.0.0 against the reference, through the fork's specs

For each of the four builds of the fork's translation (`x86_64-tables`, `i686-tables`,
`x86_64-no-tables`, `i686-no-tables`):

- `decompress_refines`: for every 32-byte input, `CompressedRistretto::decompress` returns
  without panic, overflow or divergence. The reference `decode` returns a result, and it
  rejects the input exactly when dalek does. Otherwise it returns `(x, y, 1, x y)` for the
  point `(x, y)` that the dalek result represents.
- `compress_refines`: for a point on the curve with the limb bound of the fork's spec,
  `RistrettoPoint::compress` returns the bytes of the reference `encode` of the point's
  coordinates.
- `mul_refines`: for a point on the curve with the limb bound, and a scalar `k` below `2^255`,
  `Mul<&Scalar> for &RistrettoPoint` returns a point. The reference `point_mul s` on the point's
  coordinates, with `s = k` in `ZMod l`, returns a representative of the same point, if
  `k < l` or `l • P = 0`.
- `mul_compress_refines`: for an even point `P` (a Ristretto representative) and any reference
  representative `Q` of `P`, `compress` of the dalek product returns the bytes of the
  reference `encode (point_mul s Q)`. It needs no premise `k < l`, because the two products
  differ by 4-torsion, which the encoding does not see.
- `decompress_mul_compress_refines`: the three steps end to end. If `decompress` returns a
  point, the reference `decode` returns `Ok q`, and `compress` of the dalek product returns the
  bytes of the reference `encode (point_mul s q)`.

The fork's `mul` reads the scalar as the integer of its 32 bytes, `k.asNat`, not reduced mod
`l`, with the premise `k.asNat < 2 ^ 255`. The reference reads it as an element `s` of
`ZMod l`. The theorems link the two with `(k.asNat : ZMod l) = s`.

Each theorem composes a fork spec with a reference theorem of this package. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519

namespace ForkRistretto

/-- A triple gives a result. -/
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

/-! ## Build `x86_64-tables` -/

namespace «x86_64-tables»

open Curve25519Dalek

theorem rep_toExtended (P : edwards.EdwardsPoint.«x86_64-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«x86_64-tables».toPoint_def]
  exact rep_extRef hon

/-- `CompressedRistretto::decompress` against the reference `decode`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«x86_64-tables» bytes ⦃ r =>
      ∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«x86_64-tables».toPoint) ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«x86_64-tables».decompress_spec bytes) fun r h =>
    decode_of_decodeRep bytes r _ (by rw [h.1, ristretto.CompressedRistretto.asNat_def])

/-- `RistrettoPoint::compress` against the reference `encode`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«x86_64-tables») (hP : P.LimbsLt 52)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointx86_64-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  spec_mono (ristretto.«RistrettoPointx86_64-tables».compress_spec P hP hon) fun c h =>
    encode_of_encodeRep c _ _ (rep_toExtended P hon)
      (by rw [← ristretto.CompressedRistretto.asNat_def]; exact h)

/-- `Mul<&Scalar> for &RistrettoPoint` against the reference `point_mul`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«x86_64-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255)
    (hkL : k.asNat < L ∨ L • P.toPoint = 0) :
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
      ⦃ r => (∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
        Rep q r.toPoint) ∧ r.OnCurve ∧ r.LimbsLt 52 ⦄ :=
  spec_mono («Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec
      P k hP hon hk) fun r h => by
    obtain ⟨q, hq, hrep⟩ :=
      exists_ok_of_spec (point_mul_spec_of k.asNat s hs _ _ (rep_toExtended P hon) hkL)
    exact ⟨⟨q, hq, h.2.1 ▸ hrep⟩, h.1, h.2.2⟩

/-- For an even point `P` and any reference representative `Q` of `P`, `compress` of the dalek
product `k • P` returns the bytes of the reference `encode (point_mul s Q)`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«x86_64-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointx86_64-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  spec_mono («Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul_spec
      P k hP hon hk) fun r ⟨hon', hr, hl⟩ =>
    spec_mono (ristretto.«RistrettoPointx86_64-tables».compress_spec r hl hon') fun c hc => by
      obtain ⟨q, hq, henc⟩ := exists_ok_of_spec (point_mul_encode_spec k.asNat s hs Q _ hQ hev)
      obtain ⟨c', hc', hv⟩ := exists_ok_of_spec henc
      refine ⟨q, hq, ?_⟩
      rw [hc', Array.eq_of_asNat_eq (hv.trans (hr ▸ hc.symm))]

/-- Decoding, scalar multiplication and encoding, end to end: if `decompress` returns a point
`P`, then the reference `decode` returns `Ok q`, and `compress` of the dalek product `k • P`
returns the bytes of the reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«x86_64-tables» bytes ⦃ r => ∀ P, r = some P →
      «Shared0RistrettoPointx86_64-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-tables».mul P k
        ⦃ r' => ristretto.«RistrettoPointx86_64-tables».compress r' ⦃ c =>
          ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
            ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«x86_64-tables».decompress_spec bytes) fun r h P hr => by
    obtain ⟨hmap, hpt⟩ := h
    obtain ⟨hon, hev, hl⟩ := hpt P hr
    obtain ⟨dq, hdq, hrel⟩ := decode_of_decodeRep bytes r _
      (by rw [hmap, ristretto.CompressedRistretto.asNat_def])
    rw [hr, Option.map_some] at hrel
    have hdq' := decRel_some hrel
    subst hdq'
    exact spec_mono (mul_compress_refines P k s hs hl hon hev hk _ (rep_refOf _)) fun r' h' =>
      spec_mono h' fun c ⟨q', hq', he⟩ => ⟨_, q', hdq, hq', he⟩

end «x86_64-tables»

/-! ## Build `i686-tables` -/

namespace «i686-tables»

open Curve25519Dalek

theorem rep_toExtended (P : edwards.EdwardsPoint.«i686-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«i686-tables».toPoint_def]
  exact rep_extRef hon

/-- `CompressedRistretto::decompress` against the reference `decode`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«i686-tables» bytes ⦃ r =>
      ∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«i686-tables».toPoint) ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«i686-tables».decompress_spec bytes) fun r h =>
    decode_of_decodeRep bytes r _ (by rw [h.1, ristretto.CompressedRistretto.asNat_def])

/-- `RistrettoPoint::compress` against the reference `encode`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«i686-tables») (hP : P.LimbsLt 26)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointi686-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  spec_mono (ristretto.«RistrettoPointi686-tables».compress_spec P hP hon) fun c h =>
    encode_of_encodeRep c _ _ (rep_toExtended P hon)
      (by rw [← ristretto.CompressedRistretto.asNat_def]; exact h)

/-- `Mul<&Scalar> for &RistrettoPoint` against the reference `point_mul`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«i686-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255)
    (hkL : k.asNat < L ∨ L • P.toPoint = 0) :
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
      ⦃ r => (∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
        Rep q r.toPoint) ∧ r.OnCurve ∧ r.LimbsLt 26 ⦄ :=
  spec_mono («Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul_spec
      P k hP hon hk) fun r h => by
    obtain ⟨q, hq, hrep⟩ :=
      exists_ok_of_spec (point_mul_spec_of k.asNat s hs _ _ (rep_toExtended P hon) hkL)
    exact ⟨⟨q, hq, h.2.1 ▸ hrep⟩, h.1, h.2.2⟩

/-- For an even point `P` and any reference representative `Q` of `P`, `compress` of the dalek
product `k • P` returns the bytes of the reference `encode (point_mul s Q)`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«i686-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointi686-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  spec_mono («Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul_spec
      P k hP hon hk) fun r ⟨hon', hr, hl⟩ =>
    spec_mono (ristretto.«RistrettoPointi686-tables».compress_spec r hl hon') fun c hc => by
      obtain ⟨q, hq, henc⟩ := exists_ok_of_spec (point_mul_encode_spec k.asNat s hs Q _ hQ hev)
      obtain ⟨c', hc', hv⟩ := exists_ok_of_spec henc
      refine ⟨q, hq, ?_⟩
      rw [hc', Array.eq_of_asNat_eq (hv.trans (hr ▸ hc.symm))]

/-- Decoding, scalar multiplication and encoding, end to end: if `decompress` returns a point
`P`, then the reference `decode` returns `Ok q`, and `compress` of the dalek product `k • P`
returns the bytes of the reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«i686-tables» bytes ⦃ r => ∀ P, r = some P →
      «Shared0RistrettoPointi686-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-tables».mul P k
        ⦃ r' => ristretto.«RistrettoPointi686-tables».compress r' ⦃ c =>
          ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
            ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«i686-tables».decompress_spec bytes) fun r h P hr => by
    obtain ⟨hmap, hpt⟩ := h
    obtain ⟨hon, hev, hl⟩ := hpt P hr
    obtain ⟨dq, hdq, hrel⟩ := decode_of_decodeRep bytes r _
      (by rw [hmap, ristretto.CompressedRistretto.asNat_def])
    rw [hr, Option.map_some] at hrel
    have hdq' := decRel_some hrel
    subst hdq'
    exact spec_mono (mul_compress_refines P k s hs hl hon hev hk _ (rep_refOf _)) fun r' h' =>
      spec_mono h' fun c ⟨q', hq', he⟩ => ⟨_, q', hdq, hq', he⟩

end «i686-tables»

/-! ## Build `x86_64-no-tables` -/

namespace «x86_64-no-tables»

open Curve25519Dalek

theorem rep_toExtended (P : edwards.EdwardsPoint.«x86_64-no-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def]
  exact rep_extRef hon

/-- `CompressedRistretto::decompress` against the reference `decode`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«x86_64-no-tables» bytes ⦃ r =>
      ∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint) ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«x86_64-no-tables».decompress_spec bytes) fun r h =>
    decode_of_decodeRep bytes r _ (by rw [h.1, ristretto.CompressedRistretto.asNat_def])

/-- `RistrettoPoint::compress` against the reference `encode`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«x86_64-no-tables») (hP : P.LimbsLt 52)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointx86_64-no-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  spec_mono (ristretto.«RistrettoPointx86_64-no-tables».compress_spec P hP hon) fun c h =>
    encode_of_encodeRep c _ _ (rep_toExtended P hon)
      (by rw [← ristretto.CompressedRistretto.asNat_def]; exact h)

/-- `Mul<&Scalar> for &RistrettoPoint` against the reference `point_mul`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«x86_64-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255)
    (hkL : k.asNat < L ∨ L • P.toPoint = 0) :
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
      ⦃ r => (∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
        Rep q r.toPoint) ∧ r.OnCurve ∧ r.LimbsLt 52 ⦄ :=
  spec_mono («Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul_spec
      P k hP hon hk) fun r h => by
    obtain ⟨q, hq, hrep⟩ :=
      exists_ok_of_spec (point_mul_spec_of k.asNat s hs _ _ (rep_toExtended P hon) hkL)
    exact ⟨⟨q, hq, h.2.1 ▸ hrep⟩, h.1, h.2.2⟩

/-- For an even point `P` and any reference representative `Q` of `P`, `compress` of the dalek
product `k • P` returns the bytes of the reference `encode (point_mul s Q)`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«x86_64-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 52) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointx86_64-no-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  spec_mono («Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul_spec
      P k hP hon hk) fun r ⟨hon', hr, hl⟩ =>
    spec_mono (ristretto.«RistrettoPointx86_64-no-tables».compress_spec r hl hon') fun c hc => by
      obtain ⟨q, hq, henc⟩ := exists_ok_of_spec (point_mul_encode_spec k.asNat s hs Q _ hQ hev)
      obtain ⟨c', hc', hv⟩ := exists_ok_of_spec henc
      refine ⟨q, hq, ?_⟩
      rw [hc', Array.eq_of_asNat_eq (hv.trans (hr ▸ hc.symm))]

/-- Decoding, scalar multiplication and encoding, end to end: if `decompress` returns a point
`P`, then the reference `decode` returns `Ok q`, and `compress` of the dalek product `k • P`
returns the bytes of the reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«x86_64-no-tables» bytes ⦃ r => ∀ P, r = some P →
      «Shared0RistrettoPointx86_64-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointx86_64-no-tables».mul P k
        ⦃ r' => ristretto.«RistrettoPointx86_64-no-tables».compress r' ⦃ c =>
          ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
            ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«x86_64-no-tables».decompress_spec bytes) fun r h P hr => by
    obtain ⟨hmap, hpt⟩ := h
    obtain ⟨hon, hev, hl⟩ := hpt P hr
    obtain ⟨dq, hdq, hrel⟩ := decode_of_decodeRep bytes r _
      (by rw [hmap, ristretto.CompressedRistretto.asNat_def])
    rw [hr, Option.map_some] at hrel
    have hdq' := decRel_some hrel
    subst hdq'
    exact spec_mono (mul_compress_refines P k s hs hl hon hev hk _ (rep_refOf _)) fun r' h' =>
      spec_mono h' fun c ⟨q', hq', he⟩ => ⟨_, q', hdq, hq', he⟩

end «x86_64-no-tables»

/-! ## Build `i686-no-tables` -/

namespace «i686-no-tables»

open Curve25519Dalek

theorem rep_toExtended (P : edwards.EdwardsPoint.«i686-no-tables») (hon : P.OnCurve) :
    Rep (extRef P.toExtended) P.toPoint := by
  rw [edwards.EdwardsPoint.«i686-no-tables».toPoint_def]
  exact rep_extRef hon

/-- `CompressedRistretto::decompress` against the reference `decode`. -/
theorem decompress_refines (bytes : ristretto.CompressedRistretto) :
    ristretto.CompressedRistretto.decompress.«i686-no-tables» bytes ⦃ r =>
      ∃ q, ristretto_ref.decode bytes = ok q ∧
        DecRel q (r.map edwards.EdwardsPoint.«i686-no-tables».toPoint) ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«i686-no-tables».decompress_spec bytes) fun r h =>
    decode_of_decodeRep bytes r _ (by rw [h.1, ristretto.CompressedRistretto.asNat_def])

/-- `RistrettoPoint::compress` against the reference `encode`. -/
theorem compress_refines (P : ristretto.RistrettoPoint.«i686-no-tables») (hP : P.LimbsLt 26)
    (hon : P.OnCurve) :
    ristretto.«RistrettoPointi686-no-tables».compress P ⦃ c =>
      ristretto_ref.encode (extRef P.toExtended) = ok c ⦄ :=
  spec_mono (ristretto.«RistrettoPointi686-no-tables».compress_spec P hP hon) fun c h =>
    encode_of_encodeRep c _ _ (rep_toExtended P hon)
      (by rw [← ristretto.CompressedRistretto.asNat_def]; exact h)

/-- `Mul<&Scalar> for &RistrettoPoint` against the reference `point_mul`. -/
theorem mul_refines (P : ristretto.RistrettoPoint.«i686-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hk : k.asNat < 2 ^ 255)
    (hkL : k.asNat < L ∨ L • P.toPoint = 0) :
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
      ⦃ r => (∃ q, ristretto_ref.edwards.point_mul s (extRef P.toExtended) = ok q ∧
        Rep q r.toPoint) ∧ r.OnCurve ∧ r.LimbsLt 26 ⦄ :=
  spec_mono («Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul_spec
      P k hP hon hk) fun r h => by
    obtain ⟨q, hq, hrep⟩ :=
      exists_ok_of_spec (point_mul_spec_of k.asNat s hs _ _ (rep_toExtended P hon) hkL)
    exact ⟨⟨q, hq, h.2.1 ▸ hrep⟩, h.1, h.2.2⟩

/-- For an even point `P` and any reference representative `Q` of `P`, `compress` of the dalek
product `k • P` returns the bytes of the reference `encode (point_mul s Q)`. -/
theorem mul_compress_refines (P : ristretto.RistrettoPoint.«i686-no-tables») (k : Curve25519Dalek.scalar.Scalar)
    (s : _root_.scalar.Scalar) (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s)
    (hP : P.LimbsLt 26) (hon : P.OnCurve) (hev : Even P.toPoint) (hk : k.asNat < 2 ^ 255)
    (Q : RefPt) (hQ : Rep Q P.toPoint) :
    «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
      ⦃ r => ristretto.«RistrettoPointi686-no-tables».compress r ⦃ c =>
        ∃ q, ristretto_ref.edwards.point_mul s Q = ok q ∧ ristretto_ref.encode q = ok c ⦄ ⦄ :=
  spec_mono («Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul_spec
      P k hP hon hk) fun r ⟨hon', hr, hl⟩ =>
    spec_mono (ristretto.«RistrettoPointi686-no-tables».compress_spec r hl hon') fun c hc => by
      obtain ⟨q, hq, henc⟩ := exists_ok_of_spec (point_mul_encode_spec k.asNat s hs Q _ hQ hev)
      obtain ⟨c', hc', hv⟩ := exists_ok_of_spec henc
      refine ⟨q, hq, ?_⟩
      rw [hc', Array.eq_of_asNat_eq (hv.trans (hr ▸ hc.symm))]

/-- Decoding, scalar multiplication and encoding, end to end: if `decompress` returns a point
`P`, then the reference `decode` returns `Ok q`, and `compress` of the dalek product `k • P`
returns the bytes of the reference `encode (point_mul s q)`. -/
theorem decompress_mul_compress_refines (bytes : ristretto.CompressedRistretto)
    (k : Curve25519Dalek.scalar.Scalar) (s : _root_.scalar.Scalar)
    (hs : ((k.asNat : ℕ) : ZMod _root_.scalar.l) = s) (hk : k.asNat < 2 ^ 255) :
    ristretto.CompressedRistretto.decompress.«i686-no-tables» bytes ⦃ r => ∀ P, r = some P →
      «Shared0RistrettoPointi686-no-tables».Insts.«CoreOpsArithMulSharedAScalarRistrettoPointi686-no-tables».mul P k
        ⦃ r' => ristretto.«RistrettoPointi686-no-tables».compress r' ⦃ c =>
          ∃ q q', ristretto_ref.decode bytes = ok (.Ok q) ∧
            ristretto_ref.edwards.point_mul s q = ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ ⦄ :=
  spec_mono (ristretto.CompressedRistretto.«i686-no-tables».decompress_spec bytes) fun r h P hr => by
    obtain ⟨hmap, hpt⟩ := h
    obtain ⟨hon, hev, hl⟩ := hpt P hr
    obtain ⟨dq, hdq, hrel⟩ := decode_of_decodeRep bytes r _
      (by rw [hmap, ristretto.CompressedRistretto.asNat_def])
    rw [hr, Option.map_some] at hrel
    have hdq' := decRel_some hrel
    subst hdq'
    exact spec_mono (mul_compress_refines P k s hs hl hon hev hk _ (rep_refOf _)) fun r' h' =>
      spec_mono h' fun c ⟨q', hq', he⟩ => ⟨_, q', hdq, hq', he⟩

end «i686-no-tables»

end ForkRistretto
