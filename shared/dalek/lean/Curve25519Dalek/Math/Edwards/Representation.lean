/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Funs
import Curve25519Dalek.Types
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Edwards Point Representations

Bridge infrastructure connecting Rust implementation types to the mathematical point group
`DalekSim.Edwards.Point dEd`. For each Edwards representation, we define `IsValid` predicates
and `toPoint` conversions.

## Point Representations (Edwards-specific)

- edwards.EdwardsPoint (extended coordinates)
- backend.serial.curve_models.ProjectivePoint
- backend.serial.curve_models.CompletedPoint
- backend.serial.curve_models.ProjectiveNielsPoint

Port note (ref-impl-simulation, Aeneas d119a474): `toPoint` maps to `DalekSim.Edwards.Point dEd`
(`Curve.lean`) instead of the structure `Point Ed25519`, and builds the point with `Point.mk'`.
The predicates `OnCurve` and `IsValid` and the helper lemmas are unchanged. The sections on
decompression, compression, `AffinePoint` and `CompressedEdwardsY` are not ported, because
no ported spec uses them. The commented-out variants of `ProjectiveNielsPoint.IsValid` and
`toPoint` are dropped.
-/

open DalekSim (dEd)
open DalekSim.Edwards (Point)

/-! ## EdwardsPoint validity and casting -/

namespace curve25519_dalek.edwards
open curve25519_dalek.backend.serial.u64.field Edwards

/-- Semantic curve-point invariant for the extended-coordinate representation.

Captures exactly what is needed to interpret `(X, Y, Z, T)` as a well-defined
mathematical point on Ed25519: `Z ≠ 0`, the extended coordinate relation
`T = XY/Z`, and the projective curve equation. Limb bounds live separately
in `EdwardsPoint.IsValid`. -/
@[mk_iff]
structure EdwardsPoint.OnCurve (e : EdwardsPoint) : Prop where
  /-- The Z coordinate is non-zero in the field. -/
  Z_ne_zero : e.Z.toField ≠ 0
  /-- Extended coordinate relation: T = XY/Z, i.e., XY = TZ. -/
  T_relation : e.X.toField * e.Y.toField = e.T.toField * e.Z.toField
  /-- The curve equation (twisted Edwards). -/
  on_curve :
    let X := e.X.toField; let Y := e.Y.toField; let Z := e.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance EdwardsPoint.instDecidableOnCurve (e : EdwardsPoint) : Decidable e.OnCurve :=
  decidable_of_iff _ (onCurve_iff e).symm

/-- Validity predicate for EdwardsPoint.
An EdwardsPoint (X, Y, Z, T) represents the affine point (X/Z, Y/Z) with T = XY/Z.
Bounds: all coordinates < 2^53 (needed for add operations where Y+X < 2^54).

Layered over `EdwardsPoint.OnCurve`: `IsValid` adds the per-limb bounds needed for
the underlying Rust arithmetic, while `OnCurve` carries the pure mathematical
content used by `toPoint'`. -/
@[mk_iff]
structure EdwardsPoint.IsValid (e : EdwardsPoint) : Prop extends EdwardsPoint.OnCurve e where
  /-- All coordinate limbs are bounded by 2^53. -/
  X_bounds : ∀ i < 5, e.X[i]!.val < 2 ^ 53
  Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53
  Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53
  T_bounds : ∀ i < 5, e.T[i]!.val < 2 ^ 53

instance EdwardsPoint.instDecidableIsValid (e : EdwardsPoint) : Decidable e.IsValid :=
  decidable_of_iff _ (isValid_iff e).symm

/-! ### Projective-to-affine bridge lemmas

These lemmas convert projective curve equations to the affine form
`Ed25519.a * x² + y² = 1 + Ed25519.d * x² * y²`, which is what `Point dEd`
requires for its `on_curve` field. Each representation has a different projective
shape; these lemmas clear the denominators. -/

/-- From the standard projective curve equation `a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²`
with `Z ≠ 0`, derive the affine curve equation for `(X/Z, Y/Z)`. -/
theorem affine_on_curve_of_projective
    (X Y Z : CurveField) (hZ_ne : Z ≠ 0)
    (h_curve : Ed25519.a * X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2 =
      Z ^ 4 + Ed25519.d * X ^ 2 * Y ^ 2) :
    Ed25519.a * (X / Z) ^ 2 + (Y / Z) ^ 2 =
      1 + Ed25519.d * (X / Z) ^ 2 * (Y / Z) ^ 2 := by
  simp only [Ed25519] at h_curve ⊢; simp only [div_pow]
  field_simp [pow_ne_zero 2 hZ_ne, pow_ne_zero 4 hZ_ne]
  linear_combination h_curve

/-- From the Niels-coordinate curve equation (scaled by 4 to avoid division by 2)
with `Z ≠ 0`, derive the affine curve equation for
`((YpX - YmX)/(2Z), (YpX + YmX)/(2Z))`. -/
theorem affine_on_curve_of_niels
    (YpX YmX Z : CurveField) (hZ_ne : Z ≠ 0)
    (h_curve : 4 * Ed25519.a * (YpX - YmX) ^ 2 * Z ^ 2 +
      4 * (YpX + YmX) ^ 2 * Z ^ 2 =
      16 * Z ^ 4 +
      Ed25519.d * (YpX - YmX) ^ 2 * (YpX + YmX) ^ 2) :
    Ed25519.a * ((YpX - YmX) / (2 * Z)) ^ 2 +
      ((YpX + YmX) / (2 * Z)) ^ 2 =
      1 + Ed25519.d * ((YpX - YmX) / (2 * Z)) ^ 2 *
        ((YpX + YmX) / (2 * Z)) ^ 2 := by
  have h2Z_ne : 2 * Z ≠ 0 := mul_ne_zero (by decide) hZ_ne
  simp only [Ed25519] at h_curve ⊢; simp only [div_pow]
  field_simp [pow_ne_zero 2 h2Z_ne, pow_ne_zero 4 h2Z_ne]
  ring_nf; ring_nf at h_curve; linear_combination h_curve

/-- From the completed-coordinate curve equation
`a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y²` with `Z ≠ 0` and `T ≠ 0`,
derive the affine curve equation for `(X/Z, Y/T)`. -/
theorem affine_on_curve_of_completed
    (X Y Z T : CurveField) (hZ_ne : Z ≠ 0) (hT_ne : T ≠ 0)
    (h_curve : Ed25519.a * X ^ 2 * T ^ 2 + Y ^ 2 * Z ^ 2 =
      Z ^ 2 * T ^ 2 + Ed25519.d * X ^ 2 * Y ^ 2) :
    Ed25519.a * (X / Z) ^ 2 + (Y / T) ^ 2 =
      1 + Ed25519.d * (X / Z) ^ 2 * (Y / T) ^ 2 := by
  simp only [Ed25519] at h_curve ⊢; simp only [div_pow]
  field_simp [pow_ne_zero 2 hZ_ne, pow_ne_zero 2 hT_ne]
  linear_combination h_curve

/-- Convert an EdwardsPoint to the affine point (X/Z, Y/Z).
Requires a proof that the point semantically represents a curve point
(`OnCurve`); limb bounds are not needed. -/
def EdwardsPoint.toPoint' (e : EdwardsPoint) (h : e.OnCurve) : Point dEd :=
  Point.mk' (e.X.toField / e.Z.toField)
    (e.Y.toField / e.Z.toField)
    (affine_on_curve_of_projective e.X.toField e.Y.toField e.Z.toField h.Z_ne_zero h.on_curve)

/-- Convert an EdwardsPoint to the affine point (X/Z, Y/Z).
Returns 0 if the point is not valid. -/
def EdwardsPoint.toPoint (e : EdwardsPoint) : Point dEd :=
  if h : e.IsValid then e.toPoint' h.toOnCurve else 0

/-- Unfolding lemma: when an EdwardsPoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem EdwardsPoint.toPoint_of_isValid {e : EdwardsPoint} (h : e.IsValid) :
    (e.toPoint).x = e.X.toField / e.Z.toField ∧
    (e.toPoint).y = e.Y.toField / e.Z.toField := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

end curve25519_dalek.edwards

/-! ## ProjectivePoint Validity and Casting -/

namespace curve25519_dalek.backend.serial.curve_models
open Edwards

open curve25519_dalek.backend.serial.u64.field in
/-- Semantic curve-point invariant for the projective representation.

Captures exactly what is needed to interpret `(X, Y, Z)` as a well-defined
mathematical point on Ed25519: `Z ≠ 0` and the projective curve equation.
Limb bounds live separately in `ProjectivePoint.IsValid`. -/
@[mk_iff]
structure ProjectivePoint.OnCurve (pp : ProjectivePoint) : Prop where
  /-- The Z coordinate is non-zero in the field. -/
  Z_ne_zero : pp.Z.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let X := pp.X.toField; let Y := pp.Y.toField; let Z := pp.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance ProjectivePoint.instDecidableOnCurve (pp : ProjectivePoint) : Decidable pp.OnCurve :=
  decidable_of_iff _ (onCurve_iff pp).symm

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for ProjectivePoint.
A ProjectivePoint (X, Y, Z) represents the affine point (X/Z, Y/Z).

Note: ProjectivePoint coordinates must have the tighter bound < 2^52 (not just < 2^54)
because operations like `double` compute X + Y, which must be < 2^54 for subsequent
squaring. With coords < 2^52, we get X + Y < 2^53 < 2^54.

Layered over `ProjectivePoint.OnCurve`: `IsValid` adds the per-limb bounds needed for
the underlying Rust arithmetic, while `OnCurve` carries the pure mathematical
content used by `toPoint'`. -/
@[mk_iff]
structure ProjectivePoint.IsValid (pp : ProjectivePoint) : Prop
    extends ProjectivePoint.OnCurve pp where
  /-- All coordinate limbs are bounded by 2^52. -/
  X_bounds : ∀ i < 5, pp.X[i]!.val < 2 ^ 52
  Y_bounds : ∀ i < 5, pp.Y[i]!.val < 2 ^ 52
  Z_bounds : ∀ i < 5, pp.Z[i]!.val < 2 ^ 52

instance ProjectivePoint.instDecidableIsValid (pp : ProjectivePoint) : Decidable pp.IsValid :=
  decidable_of_iff _ (isValid_iff pp).symm

open curve25519_dalek.edwards in
/-- Convert a ProjectivePoint to the affine point (X/Z, Y/Z).
Requires only `OnCurve`; limb bounds are not needed. -/
noncomputable def ProjectivePoint.toPoint' (pp : ProjectivePoint) (h : pp.OnCurve) :
    Point dEd :=
  Point.mk' (pp.X.toField / pp.Z.toField)
    (pp.Y.toField / pp.Z.toField)
    (affine_on_curve_of_projective pp.X.toField pp.Y.toField pp.Z.toField h.Z_ne_zero h.on_curve)

/-- Convert a ProjectivePoint to the affine point (X/Z, Y/Z).
Returns 0 if the point is not valid. -/
noncomputable def ProjectivePoint.toPoint (pp : ProjectivePoint) : Point dEd :=
  if h : pp.IsValid then pp.toPoint' h.toOnCurve else 0

/-- Unfolding lemma: when a ProjectivePoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem ProjectivePoint.toPoint_of_isValid {pp : ProjectivePoint} (h : pp.IsValid) :
    (pp.toPoint).x = pp.X.toField / pp.Z.toField ∧
    (pp.toPoint).y = pp.Y.toField / pp.Z.toField := by
  unfold toPoint; rw [dif_pos h]; simp only [toPoint']; trivial

/-! ## CompletedPoint Validity and Casting -/

open curve25519_dalek.backend.serial.u64.field in
/-- Semantic curve-point invariant for the completed-coordinate representation.

Captures exactly what is needed to interpret `(X, Y, Z, T)` as a well-defined
mathematical point on Ed25519 (with affine coordinates X/Z, Y/T): both `Z ≠ 0`
and `T ≠ 0`, plus the projective curve equation.
Limb bounds live separately in `CompletedPoint.IsValid`. -/
@[mk_iff]
structure CompletedPoint.OnCurve (cp : CompletedPoint) : Prop where
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : cp.Z.toField ≠ 0
  /-- The T coordinate is non-zero. -/
  T_ne_zero : cp.T.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let X := cp.X.toField; let Y := cp.Y.toField
    let Z := cp.Z.toField; let T := cp.T.toField
    Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableOnCurve (cp : CompletedPoint) : Decidable cp.OnCurve :=
  decidable_of_iff _ (onCurve_iff cp).symm

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for CompletedPoint.
A CompletedPoint (X, Y, Z, T) represents the affine point (X/Z, Y/T).
All coordinates use the universal bound < 2^54.

Layered over `CompletedPoint.OnCurve`: `IsValid` adds the per-limb bounds needed for
the underlying Rust arithmetic, while `OnCurve` carries the pure mathematical
content used by `toPoint'`. -/
@[mk_iff]
structure CompletedPoint.IsValid (cp : CompletedPoint) : Prop
    extends CompletedPoint.OnCurve cp where
  /-- All coordinate limbs are bounded by 2^54. -/
  X_valid : cp.X.IsValid
  Y_valid : cp.Y.IsValid
  Z_valid : cp.Z.IsValid
  T_valid : cp.T.IsValid

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableIsValid (cp : CompletedPoint) : Decidable cp.IsValid :=
  decidable_of_iff _ (isValid_iff cp).symm

open curve25519_dalek.edwards in
/-- Convert a CompletedPoint to the affine point (X/Z, Y/T).
Requires only `OnCurve`; limb bounds are not needed. -/
noncomputable def CompletedPoint.toPoint' (cp : CompletedPoint) (h : cp.OnCurve) :
    Point dEd :=
  Point.mk' (cp.X.toField / cp.Z.toField)
    (cp.Y.toField / cp.T.toField)
    (affine_on_curve_of_completed cp.X.toField cp.Y.toField cp.Z.toField cp.T.toField h.Z_ne_zero h.T_ne_zero h.on_curve)

/-- Convert a CompletedPoint to the affine point (X/Z, Y/T).
Returns 0 if the point is not valid. -/
noncomputable def CompletedPoint.toPoint (cp : CompletedPoint) : Point dEd :=
  if h : cp.IsValid then cp.toPoint' h.toOnCurve else 0

/-- Unfolding lemma: when a CompletedPoint is valid, toPoint computes (X/Z, Y/T). -/
theorem CompletedPoint.toPoint_of_isValid {cp : CompletedPoint} (h : cp.IsValid) :
    (cp.toPoint).x = cp.X.toField / cp.Z.toField ∧
    (cp.toPoint).y = cp.Y.toField / cp.T.toField := by
  unfold toPoint; rw [dif_pos h]; simp only [toPoint']; trivial

/-! ## ProjectiveNielsPoint Validity and Casting -/

/-- Semantic curve-point invariant for the projective-Niels representation.

Captures exactly what is needed to interpret `(Y_plus_X, Y_minus_X, Z, T2d)` as
a well-defined mathematical point on Ed25519: `Z ≠ 0`, the T2d relation, and
the projective curve equation (scaled by 4 to avoid division by 2).
Limb bounds live separately in `ProjectiveNielsPoint.IsValid`. -/
@[mk_iff]
structure ProjectiveNielsPoint.OnCurve (pn : ProjectiveNielsPoint) : Prop where
  /-- The Z coordinate is non-zero in the field. -/
  Z_ne_zero : pn.Z.toField ≠ 0
  /-- T2d relation: 2*Z*T2d = d*(YpX² - YmX²). -/
  T2d_relation :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField
    let Z := pn.Z.toField; let T2d := pn.T2d.toField
    2 * Z * T2d = Ed25519.d * (YpX^2 - YmX^2)
  /-- The curve equation (scaled by 4 to avoid 1/2). -/
  on_curve :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField; let Z := pn.Z.toField
    4 * Ed25519.a * (YpX - YmX)^2 * Z^2 + 4 * (YpX + YmX)^2 * Z^2 =
      16 * Z^4 + Ed25519.d * (YpX - YmX)^2 * (YpX + YmX)^2

instance ProjectiveNielsPoint.instDecidableOnCurve (pn : ProjectiveNielsPoint) :
    Decidable pn.OnCurve :=
  decidable_of_iff _ (onCurve_iff pn).symm

/-- Validity predicate for ProjectiveNielsPoint.

**Bounds matching Rust source profiles**: Y_plus_X < 2^54, Y_minus_X < 2^54,
Z < 2^53, T2d < 2^52.

These bounds are chosen so that `IsValid` is closed under `neg` and
`conditional_assign` while remaining as tight as Rust actually provides:
- `as_projective_niels` output: (54, 52, 53, 52) — fits within IsValid
  since 52 < 54.
- `neg` output: swaps Y_plus_X/Y_minus_X, so (52, 54, 53, 52) — fits since
  52 < 54 and T2d via `FieldElement51.negate` is < 2^52 strictly.
- `conditional_assign` output: fieldwise branchwise reuse of the same profile
  in both branches.

Producer-side sharper bounds are captured separately in
`AsProjectiveNielsProfile` (`Y_minus_X < 2^52` extra) and
`NegProfile` (`Y_plus_X < 2^52` extra) — see below.

Layered over `ProjectiveNielsPoint.OnCurve`: `IsValid` adds the per-limb bounds
needed for the underlying Rust arithmetic, while `OnCurve` carries the pure
mathematical content used by `toPoint'`. -/
@[mk_iff]
structure ProjectiveNielsPoint.IsValid (pn : ProjectiveNielsPoint) : Prop
    extends ProjectiveNielsPoint.OnCurve pn where
  /-- coordinate limbs are bounded by 2 ^ 54 2 ^ 54 2 ^ 53 2 ^ 52. -/
  Y_plus_X_bounds : ∀ i < 5, pn.Y_plus_X[i]!.val < 2 ^ 54
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < 2 ^ 54
  Z_bounds : ∀ i < 5, pn.Z[i]!.val < 2 ^ 53
  T2d_bounds : ∀ i < 5, pn.T2d[i]!.val < 2 ^ 52

instance ProjectiveNielsPoint.instDecidableIsValid (pn : ProjectiveNielsPoint) :
    Decidable pn.IsValid :=
  decidable_of_iff _ (isValid_iff pn).symm

/-- Parametric limb-bounds predicate for `ProjectiveNielsPoint`.

This is an *auxiliary* predicate for expressing exact producer/consumer
numeric profiles (e.g., the sharper bounds of `as_projective_niels`'s output)
without polluting the main `IsValid` predicate.

Use `IsValid` as the public representation invariant; use `InBounds` only
where exact limb bounds matter.

See also: `AsProjectiveNielsProfile`, `NegProfile`. -/
structure ProjectiveNielsPoint.InBounds
    (pn : ProjectiveNielsPoint) (ypxMax ymxMax zMax t2dMax : ℕ) : Prop where
  Y_plus_X_bounds  : ∀ i < 5, pn.Y_plus_X[i]!.val  < ypxMax
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < ymxMax
  Z_bounds         : ∀ i < 5, pn.Z[i]!.val         < zMax
  T2d_bounds       : ∀ i < 5, pn.T2d[i]!.val       < t2dMax

/-- The exact bound profile produced by `EdwardsPoint.as_projective_niels`:
`Y_plus_X < 2^54`, `Y_minus_X < 2^52`, `Z < 2^53`, `T2d < 2^52`. Sharper than
`IsValid` on `Y_minus_X` and `T2d`. -/
def ProjectiveNielsPoint.AsProjectiveNielsProfile (pn : ProjectiveNielsPoint) : Prop :=
  pn.InBounds (2 ^ 54) (2 ^ 52) (2 ^ 53) (2 ^ 52)

/-- The mirror of `AsProjectiveNielsProfile` produced by `neg`:
`Y_plus_X < 2^52`, `Y_minus_X < 2^54`, `Z < 2^53`, `T2d < 2^52`.
Derived from the Rust `FieldElement51::negate` output bound `< 2^52`. -/
def ProjectiveNielsPoint.NegProfile (pn : ProjectiveNielsPoint) : Prop :=
  pn.InBounds (2 ^ 52) (2 ^ 54) (2 ^ 53) (2 ^ 52)

open curve25519_dalek.edwards in
/-- Convert a ProjectiveNielsPoint to the affine point it represents.
The affine coordinates are ((Y_plus_X - Y_minus_X)/(2Z), (Y_plus_X + Y_minus_X)/(2Z)).
Requires only `OnCurve`; limb bounds are not needed. -/
noncomputable def ProjectiveNielsPoint.toPoint' (pn : ProjectiveNielsPoint) (h : pn.OnCurve) :
    Point dEd :=
  Point.mk' ((pn.Y_plus_X.toField - pn.Y_minus_X.toField) / (2 * pn.Z.toField))
    ((pn.Y_plus_X.toField + pn.Y_minus_X.toField) / (2 * pn.Z.toField))
    (affine_on_curve_of_niels pn.Y_plus_X.toField pn.Y_minus_X.toField pn.Z.toField h.Z_ne_zero h.on_curve)

/-- Convert a ProjectiveNielsPoint to the affine point it represents.
Returns 0 if the point is not valid. -/
noncomputable def ProjectiveNielsPoint.toPoint (pn : ProjectiveNielsPoint) : Point dEd :=
  if h : pn.IsValid then pn.toPoint' h.toOnCurve else 0

/-- Unfolding lemma for ProjectiveNielsPoint.toPoint. -/
theorem ProjectiveNielsPoint.toPoint_of_isValid {pn : ProjectiveNielsPoint} (h : pn.IsValid) :
    (pn.toPoint).x = (pn.Y_plus_X.toField - pn.Y_minus_X.toField) / (2 * pn.Z.toField) ∧
    (pn.toPoint).y = (pn.Y_plus_X.toField + pn.Y_minus_X.toField) / (2 * pn.Z.toField) := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

/-! ## Coercions -/

/-- Coercion allowing `q + q` syntax where `q` is a ProjectivePoint. -/
noncomputable instance : Coe ProjectivePoint (Point dEd) where
  coe p := p.toPoint

/-- Coercion allowing comparison of `CompletedPoint` results with mathematical points. -/
noncomputable instance : Coe CompletedPoint (Point dEd) where
  coe p := p.toPoint

@[simp]
theorem ProjectivePoint.toPoint_eq_coe (p : ProjectivePoint) :
    p.toPoint = ↑p := rfl

@[simp]
theorem CompletedPoint.toPoint_eq_coe (p : CompletedPoint) :
    p.toPoint = ↑p := rfl

/-! ### Shared helpers for Edwards binary operations (add / sub)

These lemmas are shared by `CompletedPoint/Add.lean` and
`ProjectiveNielsPoint/Sub.lean`. -/

/-- General on-curve lemma for completed points from affine ratios.
If `cX / cZ = Q.x` and `cY / cT = Q.y` for a curve point `Q`,
with `cZ ≠ 0` and `cT ≠ 0`, then the completed-coordinate curve
equation holds. -/
theorem completed_on_curve_of_affine_div
    (cX cY cZ cT : CurveField)
    (hcZ_ne : cZ ≠ 0) (hcT_ne : cT ≠ 0)
    (Q : Point dEd)
    (hx_eq : cX / cZ = Q.x) (hy_eq : cY / cT = Q.y) :
    Ed25519.a * cX ^ 2 * cT ^ 2 + cY ^ 2 * cZ ^ 2 =
    cZ ^ 2 * cT ^ 2 + Ed25519.d * cX ^ 2 * cY ^ 2 := by
  have hcZ2 : cZ ^ 2 ≠ 0 := pow_ne_zero 2 hcZ_ne
  have hcT2 : cT ^ 2 ≠ 0 := pow_ne_zero 2 hcT_ne
  have h_on := Q.on_curve
  calc Ed25519.a * cX ^ 2 * cT ^ 2 + cY ^ 2 * cZ ^ 2
      = (Ed25519.a * (cX / cZ) ^ 2 + (cY / cT) ^ 2) *
          cZ ^ 2 * cT ^ 2 := by field_simp [hcZ2, hcT2]
    _ = (Ed25519.a * Q.x ^ 2 + Q.y ^ 2) *
          cZ ^ 2 * cT ^ 2 := by rw [hx_eq, hy_eq]
    _ = (1 + Ed25519.d * Q.x ^ 2 * Q.y ^ 2) *
          cZ ^ 2 * cT ^ 2 := by rw [h_on]
    _ = cZ ^ 2 * cT ^ 2 +
          Ed25519.d * cX ^ 2 * cY ^ 2 := by
          rw [← hx_eq, ← hy_eq]; simp only [div_pow]
          field_simp [hcZ2, hcT2]

/-- From a Niels point's T2d relation and affine coordinate
definitions, derive `T2d = 2 * d * Z * x * y`. -/
theorem niels_T2d_affine_expr
    (YpX YmX Z T2d x y : CurveField)
    (hZ_ne : Z ≠ 0)
    (h_T2d_rel : 2 * Z * T2d =
      Ed25519.d * (YpX ^ 2 - YmX ^ 2))
    (hx : x = (YpX - YmX) / (2 * Z))
    (hy : y = (YpX + YmX) / (2 * Z)) :
    T2d = 2 * Ed25519.d * Z * x * y := by
  have h2 : (2 : CurveField) ≠ 0 := by decide
  have h2Z_ne : 2 * Z ≠ 0 := mul_ne_zero h2 hZ_ne
  have h_sq_diff : YpX ^ 2 - YmX ^ 2 =
      (YpX - YmX) * (YpX + YmX) := by ring
  have h_factor :
      (YpX - YmX) * (YpX + YmX) =
        4 * Z ^ 2 * x * y := by
    simp only [hx, hy]; field_simp [h2Z_ne]; ring
  rw [h_sq_diff, h_factor] at h_T2d_rel
  have h_simpl :
      T2d * (2 * Z) =
        2 * Ed25519.d * Z * x * y * (2 * Z) := by
    linear_combination h_T2d_rel
  field_simp [hZ_ne, h2] at h_simpl
  calc T2d = 2 * Z * Ed25519.d * x * y := h_simpl
    _ = 2 * Ed25519.d * Z * x * y := by ring

/-- From an Edwards point's T relation `X * Y = T * Z` and affine
coordinate definitions, derive `T = x * y * Z`. -/
theorem edwards_T_affine_expr
    (X Y Z T x y : CurveField)
    (hZ_ne : Z ≠ 0)
    (h_T_rel : X * Y = T * Z)
    (hx : x = X / Z) (hy : y = Y / Z) :
    T = x * y * Z := by
  simp only [hx, hy]
  field_simp [hZ_ne]
  linear_combination -h_T_rel

end curve25519_dalek.backend.serial.curve_models
