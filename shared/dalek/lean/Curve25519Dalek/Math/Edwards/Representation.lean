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
# Edwards point representations

For each Rust point type this file defines `OnCurve`, `IsValid` and a map `toPoint` to
`DalekSim.Edwards.Point dEd`. The types are `EdwardsPoint` (extended coordinates),
`ProjectivePoint`, `CompletedPoint` and `ProjectiveNielsPoint`. `OnCurve` is the mathematical
invariant. `IsValid` adds the limb bounds that the Rust arithmetic needs.

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

/-- `(X, Y, Z, T)` is a curve point: `Z ≠ 0`, `X·Y = T·Z` and the projective curve equation. -/
@[mk_iff]
structure EdwardsPoint.OnCurve (e : EdwardsPoint) : Prop where
  /-- `Z ≠ 0` in the field. -/
  Z_ne_zero : e.Z.toField ≠ 0
  /-- `X·Y = T·Z`, that is `T = XY/Z`. -/
  T_relation : e.X.toField * e.Y.toField = e.T.toField * e.Z.toField
  /-- `a·X²·Z² + Y²·Z² = Z⁴ + d·X²·Y²`. -/
  on_curve :
    let X := e.X.toField; let Y := e.Y.toField; let Z := e.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance EdwardsPoint.instDecidableOnCurve (e : EdwardsPoint) : Decidable e.OnCurve :=
  decidable_of_iff _ (onCurve_iff e).symm

/-- `OnCurve` with all limbs `< 2^53`. The point represents `(X/Z, Y/Z)`. The bound `2^53` keeps
`Y + X` in `add` below `2^54`. -/
@[mk_iff]
structure EdwardsPoint.IsValid (e : EdwardsPoint) : Prop extends EdwardsPoint.OnCurve e where
  /-- The limbs of `X` are `< 2^53`. -/
  X_bounds : ∀ i < 5, e.X[i]!.val < 2 ^ 53
  /-- The limbs of `Y` are `< 2^53`. -/
  Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53
  /-- The limbs of `Z` are `< 2^53`. -/
  Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53
  /-- The limbs of `T` are `< 2^53`. -/
  T_bounds : ∀ i < 5, e.T[i]!.val < 2 ^ 53

instance EdwardsPoint.instDecidableIsValid (e : EdwardsPoint) : Decidable e.IsValid :=
  decidable_of_iff _ (isValid_iff e).symm

/-! ### Affine curve equations

Each lemma turns the curve equation of one representation into the affine equation
`a·x² + y² = 1 + d·x²·y²` that `Point.mk'` needs. -/

/-- For `Z ≠ 0`, `a·X²·Z² + Y²·Z² = Z⁴ + d·X²·Y²` gives the affine curve equation for
`(X/Z, Y/Z)`. -/
theorem affine_on_curve_of_projective
    (X Y Z : CurveField) (hZ_ne : Z ≠ 0)
    (h_curve : Ed25519.a * X ^ 2 * Z ^ 2 + Y ^ 2 * Z ^ 2 =
      Z ^ 4 + Ed25519.d * X ^ 2 * Y ^ 2) :
    Ed25519.a * (X / Z) ^ 2 + (Y / Z) ^ 2 =
      1 + Ed25519.d * (X / Z) ^ 2 * (Y / Z) ^ 2 := by
  simp only [Ed25519] at h_curve ⊢; simp only [div_pow]
  field_simp [pow_ne_zero 2 hZ_ne, pow_ne_zero 4 hZ_ne]
  linear_combination h_curve

/-- For `Z ≠ 0`, the Niels curve equation gives the affine curve equation for
`((YpX − YmX)/(2Z), (YpX + YmX)/(2Z))`. -/
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

/-- For `Z ≠ 0` and `T ≠ 0`, `a·X²·T² + Y²·Z² = Z²·T² + d·X²·Y²` gives the affine curve
equation for `(X/Z, Y/T)`. -/
theorem affine_on_curve_of_completed
    (X Y Z T : CurveField) (hZ_ne : Z ≠ 0) (hT_ne : T ≠ 0)
    (h_curve : Ed25519.a * X ^ 2 * T ^ 2 + Y ^ 2 * Z ^ 2 =
      Z ^ 2 * T ^ 2 + Ed25519.d * X ^ 2 * Y ^ 2) :
    Ed25519.a * (X / Z) ^ 2 + (Y / T) ^ 2 =
      1 + Ed25519.d * (X / Z) ^ 2 * (Y / T) ^ 2 := by
  simp only [Ed25519] at h_curve ⊢; simp only [div_pow]
  field_simp [pow_ne_zero 2 hZ_ne, pow_ne_zero 2 hT_ne]
  linear_combination h_curve

/-- The affine point `(X/Z, Y/Z)` of an `EdwardsPoint` on the curve. -/
def EdwardsPoint.toPoint' (e : EdwardsPoint) (h : e.OnCurve) : Point dEd :=
  Point.mk' (e.X.toField / e.Z.toField)
    (e.Y.toField / e.Z.toField)
    (affine_on_curve_of_projective e.X.toField e.Y.toField e.Z.toField h.Z_ne_zero h.on_curve)

/-- The affine point `(X/Z, Y/Z)` of a valid `EdwardsPoint`, and `0` otherwise. -/
def EdwardsPoint.toPoint (e : EdwardsPoint) : Point dEd :=
  if h : e.IsValid then e.toPoint' h.toOnCurve else 0

/-- For valid `e`, `e.toPoint = (X/Z, Y/Z)`. -/
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
/-- `(X, Y, Z)` is a curve point: `Z ≠ 0` and the projective curve equation. -/
@[mk_iff]
structure ProjectivePoint.OnCurve (pp : ProjectivePoint) : Prop where
  /-- `Z ≠ 0` in the field. -/
  Z_ne_zero : pp.Z.toField ≠ 0
  /-- `a·X²·Z² + Y²·Z² = Z⁴ + d·X²·Y²`. -/
  on_curve :
    let X := pp.X.toField; let Y := pp.Y.toField; let Z := pp.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance ProjectivePoint.instDecidableOnCurve (pp : ProjectivePoint) : Decidable pp.OnCurve :=
  decidable_of_iff _ (onCurve_iff pp).symm

open curve25519_dalek.backend.serial.u64.field in
/-- `OnCurve` with all limbs `< 2^52`. The point represents `(X/Z, Y/Z)`. The bound implies the
bound `X, Y < 2^53` that `double` needs. -/
@[mk_iff]
structure ProjectivePoint.IsValid (pp : ProjectivePoint) : Prop
    extends ProjectivePoint.OnCurve pp where
  /-- The limbs of `X` are `< 2^52`. -/
  X_bounds : ∀ i < 5, pp.X[i]!.val < 2 ^ 52
  /-- The limbs of `Y` are `< 2^52`. -/
  Y_bounds : ∀ i < 5, pp.Y[i]!.val < 2 ^ 52
  /-- The limbs of `Z` are `< 2^52`. -/
  Z_bounds : ∀ i < 5, pp.Z[i]!.val < 2 ^ 52

instance ProjectivePoint.instDecidableIsValid (pp : ProjectivePoint) : Decidable pp.IsValid :=
  decidable_of_iff _ (isValid_iff pp).symm

open curve25519_dalek.edwards in
/-- The affine point `(X/Z, Y/Z)` of a `ProjectivePoint` on the curve. -/
noncomputable def ProjectivePoint.toPoint' (pp : ProjectivePoint) (h : pp.OnCurve) :
    Point dEd :=
  Point.mk' (pp.X.toField / pp.Z.toField)
    (pp.Y.toField / pp.Z.toField)
    (affine_on_curve_of_projective pp.X.toField pp.Y.toField pp.Z.toField h.Z_ne_zero h.on_curve)

/-- The affine point `(X/Z, Y/Z)` of a valid `ProjectivePoint`, and `0` otherwise. -/
noncomputable def ProjectivePoint.toPoint (pp : ProjectivePoint) : Point dEd :=
  if h : pp.IsValid then pp.toPoint' h.toOnCurve else 0

/-- For valid `pp`, `pp.toPoint = (X/Z, Y/Z)`. -/
theorem ProjectivePoint.toPoint_of_isValid {pp : ProjectivePoint} (h : pp.IsValid) :
    (pp.toPoint).x = pp.X.toField / pp.Z.toField ∧
    (pp.toPoint).y = pp.Y.toField / pp.Z.toField := by
  unfold toPoint; rw [dif_pos h]; simp only [toPoint']; trivial

/-! ## CompletedPoint Validity and Casting -/

open curve25519_dalek.backend.serial.u64.field in
/-- `(X, Y, Z, T)` is a curve point with affine coordinates `(X/Z, Y/T)`: `Z ≠ 0`, `T ≠ 0` and
the completed curve equation. -/
@[mk_iff]
structure CompletedPoint.OnCurve (cp : CompletedPoint) : Prop where
  /-- `Z ≠ 0` in the field. -/
  Z_ne_zero : cp.Z.toField ≠ 0
  /-- `T ≠ 0` in the field. -/
  T_ne_zero : cp.T.toField ≠ 0
  /-- `a·X²·T² + Y²·Z² = Z²·T² + d·X²·Y²`. -/
  on_curve :
    let X := cp.X.toField; let Y := cp.Y.toField
    let Z := cp.Z.toField; let T := cp.T.toField
    Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableOnCurve (cp : CompletedPoint) : Decidable cp.OnCurve :=
  decidable_of_iff _ (onCurve_iff cp).symm

open curve25519_dalek.backend.serial.u64.field in
/-- `OnCurve` with all limbs `< 2^54` (`FieldElement51.IsValid`). The point represents
`(X/Z, Y/T)`. -/
@[mk_iff]
structure CompletedPoint.IsValid (cp : CompletedPoint) : Prop
    extends CompletedPoint.OnCurve cp where
  /-- The limbs of `X` are `< 2^54`. -/
  X_valid : cp.X.IsValid
  /-- The limbs of `Y` are `< 2^54`. -/
  Y_valid : cp.Y.IsValid
  /-- The limbs of `Z` are `< 2^54`. -/
  Z_valid : cp.Z.IsValid
  /-- The limbs of `T` are `< 2^54`. -/
  T_valid : cp.T.IsValid

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableIsValid (cp : CompletedPoint) : Decidable cp.IsValid :=
  decidable_of_iff _ (isValid_iff cp).symm

open curve25519_dalek.edwards in
/-- The affine point `(X/Z, Y/T)` of a `CompletedPoint` on the curve. -/
noncomputable def CompletedPoint.toPoint' (cp : CompletedPoint) (h : cp.OnCurve) :
    Point dEd :=
  Point.mk' (cp.X.toField / cp.Z.toField)
    (cp.Y.toField / cp.T.toField)
    (affine_on_curve_of_completed cp.X.toField cp.Y.toField cp.Z.toField cp.T.toField h.Z_ne_zero h.T_ne_zero h.on_curve)

/-- The affine point `(X/Z, Y/T)` of a valid `CompletedPoint`, and `0` otherwise. -/
noncomputable def CompletedPoint.toPoint (cp : CompletedPoint) : Point dEd :=
  if h : cp.IsValid then cp.toPoint' h.toOnCurve else 0

/-- For valid `cp`, `cp.toPoint = (X/Z, Y/T)`. -/
theorem CompletedPoint.toPoint_of_isValid {cp : CompletedPoint} (h : cp.IsValid) :
    (cp.toPoint).x = cp.X.toField / cp.Z.toField ∧
    (cp.toPoint).y = cp.Y.toField / cp.T.toField := by
  unfold toPoint; rw [dif_pos h]; simp only [toPoint']; trivial

/-! ## ProjectiveNielsPoint Validity and Casting -/

/-- `(YpX, YmX, Z, T2d)` is a curve point: `Z ≠ 0`, `2·Z·T2d = d·(YpX² − YmX²)` and the curve
equation for `((YpX − YmX)/(2Z), (YpX + YmX)/(2Z))` with denominators cleared. -/
@[mk_iff]
structure ProjectiveNielsPoint.OnCurve (pn : ProjectiveNielsPoint) : Prop where
  /-- `Z ≠ 0` in the field. -/
  Z_ne_zero : pn.Z.toField ≠ 0
  /-- `2·Z·T2d = d·(YpX² − YmX²)`. -/
  T2d_relation :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField
    let Z := pn.Z.toField; let T2d := pn.T2d.toField
    2 * Z * T2d = Ed25519.d * (YpX^2 - YmX^2)
  /-- The affine curve equation multiplied by `16·Z⁴`. -/
  on_curve :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField; let Z := pn.Z.toField
    4 * Ed25519.a * (YpX - YmX)^2 * Z^2 + 4 * (YpX + YmX)^2 * Z^2 =
      16 * Z^4 + Ed25519.d * (YpX - YmX)^2 * (YpX + YmX)^2

instance ProjectiveNielsPoint.instDecidableOnCurve (pn : ProjectiveNielsPoint) :
    Decidable pn.OnCurve :=
  decidable_of_iff _ (onCurve_iff pn).symm

/-- `OnCurve` with limbs `Y_plus_X, Y_minus_X < 2^54`, `Z < 2^53` and `T2d < 2^52`. These bounds
cover the output of `as_projective_niels` and of `neg`, which swaps `Y_plus_X` and `Y_minus_X`.
So `IsValid` is closed under `neg` and `conditional_assign`. -/
@[mk_iff]
structure ProjectiveNielsPoint.IsValid (pn : ProjectiveNielsPoint) : Prop
    extends ProjectiveNielsPoint.OnCurve pn where
  /-- The limbs of `Y_plus_X` are `< 2^54`. -/
  Y_plus_X_bounds : ∀ i < 5, pn.Y_plus_X[i]!.val < 2 ^ 54
  /-- The limbs of `Y_minus_X` are `< 2^54`. -/
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < 2 ^ 54
  /-- The limbs of `Z` are `< 2^53`. -/
  Z_bounds : ∀ i < 5, pn.Z[i]!.val < 2 ^ 53
  /-- The limbs of `T2d` are `< 2^52`. -/
  T2d_bounds : ∀ i < 5, pn.T2d[i]!.val < 2 ^ 52

instance ProjectiveNielsPoint.instDecidableIsValid (pn : ProjectiveNielsPoint) :
    Decidable pn.IsValid :=
  decidable_of_iff _ (isValid_iff pn).symm

/-- Limb bounds `Y_plus_X < ypxMax`, `Y_minus_X < ymxMax`, `Z < zMax` and `T2d < t2dMax`. It
states bounds sharper than `IsValid`. -/
structure ProjectiveNielsPoint.InBounds
    (pn : ProjectiveNielsPoint) (ypxMax ymxMax zMax t2dMax : ℕ) : Prop where
  Y_plus_X_bounds  : ∀ i < 5, pn.Y_plus_X[i]!.val  < ypxMax
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < ymxMax
  Z_bounds         : ∀ i < 5, pn.Z[i]!.val         < zMax
  T2d_bounds       : ∀ i < 5, pn.T2d[i]!.val       < t2dMax

/-- The bounds of the output of `EdwardsPoint.as_projective_niels`: `Y_plus_X < 2^54`,
`Y_minus_X < 2^52`, `Z < 2^53` and `T2d < 2^52`. -/
def ProjectiveNielsPoint.AsProjectiveNielsProfile (pn : ProjectiveNielsPoint) : Prop :=
  pn.InBounds (2 ^ 54) (2 ^ 52) (2 ^ 53) (2 ^ 52)

/-- `AsProjectiveNielsProfile` with `Y_plus_X` and `Y_minus_X` swapped: `Y_plus_X < 2^52`,
`Y_minus_X < 2^54`, `Z < 2^53` and `T2d < 2^52`. -/
def ProjectiveNielsPoint.NegProfile (pn : ProjectiveNielsPoint) : Prop :=
  pn.InBounds (2 ^ 52) (2 ^ 54) (2 ^ 53) (2 ^ 52)

open curve25519_dalek.edwards in
/-- The affine point `((YpX − YmX)/(2Z), (YpX + YmX)/(2Z))` of a `ProjectiveNielsPoint` on the
curve. -/
noncomputable def ProjectiveNielsPoint.toPoint' (pn : ProjectiveNielsPoint) (h : pn.OnCurve) :
    Point dEd :=
  Point.mk' ((pn.Y_plus_X.toField - pn.Y_minus_X.toField) / (2 * pn.Z.toField))
    ((pn.Y_plus_X.toField + pn.Y_minus_X.toField) / (2 * pn.Z.toField))
    (affine_on_curve_of_niels pn.Y_plus_X.toField pn.Y_minus_X.toField pn.Z.toField h.Z_ne_zero h.on_curve)

/-- The affine point `((YpX − YmX)/(2Z), (YpX + YmX)/(2Z))` of a valid `ProjectiveNielsPoint`,
and `0` otherwise. -/
noncomputable def ProjectiveNielsPoint.toPoint (pn : ProjectiveNielsPoint) : Point dEd :=
  if h : pn.IsValid then pn.toPoint' h.toOnCurve else 0

/-- For valid `pn`, `pn.toPoint = ((YpX − YmX)/(2Z), (YpX + YmX)/(2Z))`. -/
theorem ProjectiveNielsPoint.toPoint_of_isValid {pn : ProjectiveNielsPoint} (h : pn.IsValid) :
    (pn.toPoint).x = (pn.Y_plus_X.toField - pn.Y_minus_X.toField) / (2 * pn.Z.toField) ∧
    (pn.toPoint).y = (pn.Y_plus_X.toField + pn.Y_minus_X.toField) / (2 * pn.Z.toField) := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

/-! ## Coercions -/

/-- A `ProjectivePoint` coerces to `Point dEd` by `toPoint`. -/
noncomputable instance : Coe ProjectivePoint (Point dEd) where
  coe p := p.toPoint

/-- A `CompletedPoint` coerces to `Point dEd` by `toPoint`. -/
noncomputable instance : Coe CompletedPoint (Point dEd) where
  coe p := p.toPoint

/-- `p.toPoint` is the coercion `↑p`. -/
@[simp]
theorem ProjectivePoint.toPoint_eq_coe (p : ProjectivePoint) :
    p.toPoint = ↑p := rfl

/-- `p.toPoint` is the coercion `↑p`. -/
@[simp]
theorem CompletedPoint.toPoint_eq_coe (p : CompletedPoint) :
    p.toPoint = ↑p := rfl

/-! ### Helpers for point addition -/

/-- For `cZ ≠ 0`, `cT ≠ 0`, `cX/cZ = Q.x` and `cY/cT = Q.y`, `(cX, cY, cZ, cT)` satisfies the
completed curve equation. -/
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

/-- For `Z ≠ 0`, `2·Z·T2d = d·(YpX² − YmX²)`, `x = (YpX − YmX)/(2Z)` and `y = (YpX + YmX)/(2Z)`,
`T2d = 2·d·Z·x·y`. -/
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

/-- For `Z ≠ 0`, `X·Y = T·Z`, `x = X/Z` and `y = Y/Z`, `T = x·y·Z`. -/
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
