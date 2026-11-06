import Mathlib.Algebra.Field.Basic

/-! # The reference Montgomery ladder as a pure function

`lstep x1 b` is one iteration of the reference ladder of `tracks/x25519/ref-plain` with key bit
`b`: swap the two points if `b`, apply `pad x1`, swap back. `ladder x1 bits` folds `lstep` over
`bits`, most significant first. `enc` is the affine u-coordinate `x / z` with `x / 0 = 0`.

`ForkSim.montgomery_ladder_eq` shows that the translated reference ladder computes `ladder`
over bits 255 to 0 of its scalar argument. `ForkSim.toPair_ladderLoop` shows that the fork's
ladder, which swaps lazily, computes `ladder` over bits `t - 1` to 0 of its scalar when it
runs `t` iterations.

The definitions come from track B (`tracks/x25519/lean/Sim/LadderMath.lean`). -/

namespace ForkSim.LadderMath

variable {R : Type*} [CommRing R]

/-- A point in projective `(x : z)` coordinates. -/
abbrev Pt (R : Type*) := R × R

/-- The doubling half of the RFC 7748 ladder step. -/
def dbl (P : Pt R) : Pt R :=
  ((P.1 + P.2) ^ 2 * ((P.1 - P.2) * (P.1 - P.2)),
   ((P.1 + P.2) ^ 2 - (P.1 - P.2) * (P.1 - P.2)) *
     ((P.1 + P.2) ^ 2 + 121665 * ((P.1 + P.2) ^ 2 - (P.1 - P.2) * (P.1 - P.2))))

/-- The differential addition half of the RFC 7748 ladder step. `x1` is the u-coordinate of
the difference of the two points. -/
def dadd (x1 : R) (P Q : Pt R) : Pt R :=
  (((Q.1 - Q.2) * (P.1 + P.2) + (Q.1 + Q.2) * (P.1 - P.2)) ^ 2,
   x1 * ((Q.1 - Q.2) * (P.1 + P.2) - (Q.1 + Q.2) * (P.1 - P.2)) ^ 2)

/-- One ladder step without swaps: `x25519_ref.point_add_and_double` in closed form. -/
def pad (x1 : R) (S : Pt R × Pt R) : Pt R × Pt R := (dbl S.1, dadd x1 S.1 S.2)

/-- Swap the two points if `b`. -/
def cswap {α : Type*} (b : Bool) (S : α × α) : α × α := if b then (S.2, S.1) else S

/-- One ladder iteration with key bit `b`: swap, step, swap back. -/
def lstep (x1 : R) (b : Bool) (S : Pt R × Pt R) : Pt R × Pt R := cswap b (pad x1 (cswap b S))

/-- The ladder over a list of key bits, most significant first. -/
def ladder (x1 : R) (bits : List Bool) (S : Pt R × Pt R) : Pt R × Pt R :=
  bits.foldl (fun S b => lstep x1 b S) S

@[simp] theorem ladder_nil (x1 : R) (S : Pt R × Pt R) : ladder x1 [] S = S := rfl

@[simp] theorem ladder_cons (x1 : R) (b : Bool) (bits : List Bool) (S : Pt R × Pt R) :
    ladder x1 (b :: bits) S = ladder x1 bits (lstep x1 b S) := rfl

/-- The affine u-coordinate `x / z`, with `x / 0 = 0` as `fe_inv` gives. -/
def enc {K : Type*} [Field K] (P : Pt K) : K := P.1 * P.2⁻¹

end ForkSim.LadderMath
