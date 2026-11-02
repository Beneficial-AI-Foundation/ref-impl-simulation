import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # The Montgomery ladder as a pure function

The reference and dalek compute the same ladder step on field elements (`Sim/Pilot.lean`).
They differ in two places:

1. The reference runs 256 iterations, from bit 255. dalek runs 255 iterations, from bit 254.
   The masked scalar has bit 255 equal to 0, so the reference does one more step with bit 0.
2. dalek swaps lazily. `Sim/Full.lean` shows that its logical state follows `lstep`.

This file shows that the extra step does not change the encoded result. After the extra step,
the second point of the reference state is the dalek point times `4 u`. A step multiplies each
point by a nonzero factor when the factors start nonzero (`Rel`). The encoding `x / z` cancels
the factor. If `u = 0`, both encodings are 0 (`zero_case`).

Everything here is over an arbitrary commutative ring `R`, or a field for the last part. -/

namespace X25519Sim.LadderMath

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

/-- `cswap b ∘ cswap a = cswap (a ^^ b)`. -/
theorem cswap_cswap {α : Type*} (a b : Bool) (S : α × α) :
    cswap b (cswap a S) = cswap (a ^^ b) S := by
  cases a <;> cases b <;> rfl

/-- Scale a projective point. -/
def smul (a : R) (P : Pt R) : Pt R := (a * P.1, a * P.2)

/-- Doubling is homogeneous of degree 4: `dbl (a • P) = a⁴ • dbl P`. -/
theorem dbl_smul (a : R) (P : Pt R) : dbl (smul a P) = smul (a ^ 4) (dbl P) := by
  simp only [dbl, smul, Prod.mk.injEq]; constructor <;> ring

/-- Differential addition is homogeneous of degree 2 in each point:
`dadd x1 (a • P) (b • Q) = (a b)² • dadd x1 P Q`. -/
theorem dadd_smul (x1 a b : R) (P Q : Pt R) :
    dadd x1 (smul a P) (smul b Q) = smul ((a * b) ^ 2) (dadd x1 P Q) := by
  simp only [dadd, smul, Prod.mk.injEq]; constructor <;> ring

/-- `dadd_smul` with the points in the order `(Q, P)`. -/
theorem dadd_smul' (x1 a b : R) (P Q : Pt R) :
    dadd x1 (smul b Q) (smul a P) = smul ((a * b) ^ 2) (dadd x1 Q P) := by
  rw [dadd_smul, mul_comm b a]

section Domain
variable [IsDomain R]

/-- `S` is `T` with each point scaled by a nonzero factor. -/
def Rel (S T : Pt R × Pt R) : Prop :=
  ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ S = (smul a T.1, smul b T.2)

/-- One ladder iteration preserves `Rel`. -/
theorem lstep_rel (x1 : R) (bit : Bool) {S T : Pt R × Pt R} (h : Rel S T) :
    Rel (lstep x1 bit S) (lstep x1 bit T) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  cases bit
  · refine ⟨a ^ 4, (a * b) ^ 2, pow_ne_zero _ ha, pow_ne_zero _ (mul_ne_zero ha hb), ?_⟩
    simp only [lstep, cswap, pad, dbl_smul, dadd_smul, Bool.false_eq_true, if_false]
  · refine ⟨(a * b) ^ 2, b ^ 4, pow_ne_zero _ (mul_ne_zero ha hb), pow_ne_zero _ hb, ?_⟩
    simp only [lstep, cswap, pad, dbl_smul, dadd_smul', if_true]

/-- The ladder preserves `Rel`: if `Rel S T`, then `Rel (ladder x1 bits S) (ladder x1 bits T)`. -/
theorem ladder_rel (x1 : R) (bits : List Bool) {S T : Pt R × Pt R} (h : Rel S T) :
    Rel (ladder x1 bits S) (ladder x1 bits T) := by
  induction bits generalizing S T with
  | nil => exact h
  | cons b bits ih => exact ih (lstep_rel x1 b h)

end Domain

/-! ## The case `x1 = 0` -/

/-- Each point satisfies `x * z = 0`. -/
def Degenerate (S : Pt R × Pt R) : Prop := S.1.1 * S.1.2 = 0 ∧ S.2.1 * S.2.2 = 0

/-- If `x * z = 0`, then the doubled point has `z = 0`. -/
theorem dbl_z_of_degenerate (P : Pt R) (h : P.1 * P.2 = 0) : (dbl P).2 = 0 := by
  have : (P.1 + P.2) ^ 2 - (P.1 - P.2) * (P.1 - P.2) = 4 * (P.1 * P.2) := by ring
  simp only [dbl, this, h, mul_zero, zero_mul]

/-- With `x1 = 0`, the sum has `z = 0`. -/
theorem dadd_z_zero (P Q : Pt R) : (dadd 0 P Q).2 = 0 := by
  simp only [dadd, zero_mul]

/-- With `x1 = 0`, one iteration from a degenerate state gives both points `z = 0`. -/
theorem lstep_zero (bit : Bool) (S : Pt R × Pt R) (h : Degenerate S) :
    (lstep 0 bit S).1.2 = 0 ∧ (lstep 0 bit S).2.2 = 0 := by
  obtain ⟨h1, h2⟩ := h
  cases bit
  · simp only [lstep, cswap, pad, Bool.false_eq_true, if_false]
    exact ⟨dbl_z_of_degenerate _ h1, dadd_z_zero _ _⟩
  · simp only [lstep, cswap, pad, if_true]
    exact ⟨dadd_z_zero _ _, dbl_z_of_degenerate _ h2⟩

/-- A state whose two points have `z = 0` is degenerate. -/
theorem degenerate_of_z (S : Pt R × Pt R) (h : S.1.2 = 0 ∧ S.2.2 = 0) : Degenerate S := by
  simp only [Degenerate, h.1, h.2, mul_zero, and_self]

/-- With `x1 = 0`, a degenerate state stays degenerate, and after at least one step both `z`
coordinates are 0. -/
theorem ladder_zero (bits : List Bool) (S : Pt R × Pt R) (h : Degenerate S) (hne : bits ≠ []) :
    (ladder 0 bits S).1.2 = 0 ∧ (ladder 0 bits S).2.2 = 0 := by
  induction bits generalizing S with
  | nil => exact absurd rfl hne
  | cons b bits ih =>
    rw [ladder_cons]
    have hs := lstep_zero b S h
    cases bits with
    | nil => exact hs
    | cons _ _ => exact ih _ (degenerate_of_z _ hs) (List.cons_ne_nil _ _)

/-! ## The encoding -/

section Field
variable {K : Type*} [Field K]

/-- The affine u-coordinate `x / z`, with `x / 0 = 0` as `fe_inv` gives. -/
def enc (P : Pt K) : K := P.1 * P.2⁻¹

/-- For `a ≠ 0`, `enc (a • P) = enc P`. -/
theorem enc_smul (a : K) (ha : a ≠ 0) (P : Pt K) : enc (smul a P) = enc P := by
  simp only [enc, smul, mul_inv]
  calc a * P.1 * (a⁻¹ * P.2⁻¹) = (a * a⁻¹) * (P.1 * P.2⁻¹) := by ring
    _ = P.1 * P.2⁻¹ := by rw [mul_inv_cancel₀ ha, one_mul]

/-- If `z = 0`, then `enc P = 0`. -/
theorem enc_z_zero (P : Pt K) (h : P.2 = 0) : enc P = 0 := by
  simp only [enc, h, inv_zero, mul_zero]

/-- The first reference step with bit 0, from `((1, 0), (u, 1))`. -/
theorem lstep_first (u : K) :
    lstep u false ((1, 0), (u, 1)) = (smul 1 (1, 0), smul (4 * u) (u, 1)) := by
  simp only [lstep, cswap, pad, dbl, dadd, smul, Bool.false_eq_true, if_false, Prod.mk.injEq]
  refine ⟨⟨by ring, by ring⟩, by ring, by ring⟩

/-- **The extra reference step does not change the result.** `bits` are the 255 dalek bits.
The reference runs bit 255, which is 0 for a masked scalar, and then the same bits. -/
theorem enc_ladder_extra_step (u : K) (h4 : (4 : K) ≠ 0) (bits : List Bool) (hne : bits ≠ []) :
    enc (ladder u (false :: bits) ((1, 0), (u, 1))).1 = enc (ladder u bits ((1, 0), (u, 1))).1 := by
  rw [ladder_cons, lstep_first]
  by_cases hu : u = 0
  · subst hu
    have hdeg : Degenerate (((1 : K), (0 : K)), ((0 : K), (1 : K))) := by
      simp [Degenerate]
    have hdeg' : Degenerate (smul (1 : K) ((1 : K), (0 : K)), smul (4 * (0 : K)) ((0 : K), 1)) := by
      simp [Degenerate, smul]
    rw [enc_z_zero _ (ladder_zero bits _ hdeg' hne).1, enc_z_zero _ (ladder_zero bits _ hdeg hne).1]
  · have hrel : Rel (smul (1 : K) (1, 0), smul (4 * u) (u, 1)) ((1, 0), (u, 1)) :=
      ⟨1, 4 * u, one_ne_zero, mul_ne_zero h4 hu, rfl⟩
    obtain ⟨a, b, ha, _, heq⟩ := ladder_rel u bits hrel
    rw [heq, enc_smul a ha]

end Field

end X25519Sim.LadderMath
