/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Markus Dablander
-/
import Curve25519Dalek.Math.Basic
import DalekSim.Edwards
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Edwards curve parameters and the point group

`EdwardsCurve` and `Ed25519` are the curve parameters `a = -1` and `d` of edwards25519. The
specs state the curve equation of each point representation with them.

Port note (ref-impl-simulation, Aeneas d119a474): curve25519-dalek-lean-verify defines its own
structure `Point Ed25519` and its group law in this file. Its associativity is a `sorry`. This
port keeps `EdwardsCurve` and `Ed25519` and drops the rest. The specs use the group
`DalekSim.Edwards.Point dEd`, which has the same addition formula and a proof of associativity
with the standard axioms. The section `Point` gives that type the interface of the old one:
`x`, `y`, `on_curve`, `mk'`, `ext`, and the lemmas `add_x`, `add_y`, `zero_x`, `zero_y`,
`neg_x`, `neg_y` and `denomsNeZero` with the same statements.
-/

namespace Edwards

open ZMod

instance : NeZero (2 : CurveField) := ⟨by decide⟩

/-- A Twisted Edwards curve structure defined by parameters a and d. -/
structure EdwardsCurve (F : Type) where
  a : F
  d : F

/-- The specific Ed25519 curve parameters lifted to the field. -/
def Ed25519 : EdwardsCurve CurveField := {
  a := -1,
  d := (d : CurveField)
}

theorem Ed25519_a : Ed25519.a = -1 := rfl

theorem Ed25519_d : Ed25519.d = DalekSim.dEd := rfl

/-- `(a : CurveField) ≡ (b : CurveField)` iff `a ≡ b [MOD p]`. -/
theorem lift_mod_eq_iff (a b : ℕ) : (a ≡ b [MOD p]) ↔ (a : CurveField) = (b : CurveField) := by
  rw [Nat.ModEq]
  exact (ZMod.natCast_eq_natCast_iff a b p).symm

end Edwards

namespace DalekSim.Edwards.Point

open _root_.Edwards

/-! ## The point group `Point dEd` with the interface of the old `Point Ed25519` -/

/-- The x-coordinate. -/
def x (P : Point dEd) : CurveField := P.1.1

/-- The y-coordinate. -/
def y (P : Point dEd) : CurveField := P.1.2

/-- The curve equation, in the form `a x² + y² = 1 + d x² y²`. -/
theorem on_curve (P : Point dEd) :
    Ed25519.a * P.x ^ 2 + P.y ^ 2 = 1 + Ed25519.d * P.x ^ 2 * P.y ^ 2 := by
  have h := P.2
  simp only [OnCurve] at h
  simp only [x, y, Ed25519_a, Ed25519_d]
  linear_combination h

/-- The point `(x, y)`, from the curve equation in the form `a x² + y² = 1 + d x² y²`. -/
def mk' (x y : CurveField)
    (h : Ed25519.a * x ^ 2 + y ^ 2 = 1 + Ed25519.d * x ^ 2 * y ^ 2) : Point dEd :=
  ⟨(x, y), by simp only [OnCurve]; simp only [Ed25519_a, Ed25519_d] at h; linear_combination h⟩

@[simp] theorem x_mk' (x y : CurveField) (h) : (mk' x y h).x = x := rfl

@[simp] theorem y_mk' (x y : CurveField) (h) : (mk' x y h).y = y := rfl

theorem ext_xy {P Q : Point dEd} (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q :=
  Point.ext (Prod.ext hx hy)

theorem mk'_inj {x₁ y₁ x₂ y₂ : CurveField} {h₁ h₂} :
    mk' x₁ y₁ h₁ = mk' x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h; exact ⟨congrArg x h, congrArg y h⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem zero_x : (0 : Point dEd).x = 0 := rfl

@[simp] theorem zero_y : (0 : Point dEd).y = 1 := rfl

@[simp] theorem neg_x (P : Point dEd) : (-P).x = -P.x := rfl

@[simp] theorem neg_y (P : Point dEd) : (-P).y = P.y := rfl

/-- The x-coordinate of `p + q`. -/
theorem add_x (p q : Point dEd) :
    (p + q).x = (p.x * q.y + p.y * q.x) / (1 + Ed25519.d * p.x * q.x * p.y * q.y) := rfl

/-- The y-coordinate of `p + q`. -/
theorem add_y (p q : Point dEd) :
    (p + q).y =
      (p.y * q.y - Ed25519.a * p.x * q.x) / (1 - Ed25519.d * p.x * q.x * p.y * q.y) := by
  change (p.y * q.y + p.x * q.x) / (1 - Ed25519.d * p.x * q.x * p.y * q.y) = _
  rw [Ed25519_a]; ring

/-- The two denominators of the addition formula are not 0. -/
theorem denomsNeZero (p1 p2 : Point dEd) :
    let lamVal := Ed25519.d * p1.x * p2.x * p1.y * p2.y
    (1 + lamVal ≠ 0) ∧ (1 - lamVal ≠ 0) :=
  ⟨one_add_ne_zero (d := dEd) p1.2 p2.2, one_sub_ne_zero (d := dEd) p1.2 p2.2⟩

end DalekSim.Edwards.Point
