import Sim.EdwardsBridge

/-! # The Montgomery ladder computes multiples on the Edwards curve

The Edwards point `(x, y)` has the projective Montgomery point `rep (x, y) = (1 + y : 1 - y)`.
Its encoding is `toU y`, and the identity `(0, 1)` has `rep = (2 : 0)` and the encoding 0.

On `-x² + y² = 1 + d x² y²` with `Complete d` and `121666 d = -121665`:

1. `dbl_rep`: `dbl (rep P)` is `rep (P + P)` times a nonzero factor, for every point `P`.
2. `dadd_rep`: `dadd u (rep P) (rep Q)` is `rep (P + Q)` times a nonzero factor, if
   `u (1 - y_D) = 1 + y_D` for the y-coordinate `y_D` of `P - Q`, and `u ≠ 0`. Both the
   identity and `(0, -1)` have `toU = 0`, so the hypotheses exclude `P = Q` and
   `P - Q = (0, -1)`. `P`, `Q` or `P + Q` can be the identity, and `P` and `Q` can be
   negatives of each other.
3. `ladder_rep`: if `u ≠ 0` is the u-coordinate of `B`, the ladder over `bits` takes
   `(n • B, (n + 1) • B)` to `(m • B, (m + 1) • B)` with `m = bitsVal n bits`, up to nonzero
   factors. The difference of the two points is always `B`, so `dadd_rep` applies at each
   step.
4. `enc_ladder`: from `((1 : 0), (u : 1))`, the first point encodes `toU (m • B)`.

The section `Curve25519` gives the base point `B` of edwards25519, with `toU y = 9`, and
`enc_ladder_nine`. The projective invariant covers the identity inside the ladder with
nonzero factors. Only the final encoding uses `a⁻¹ = 0` for `a = 0`, where `toU` of the
identity is 0. -/

namespace X25519Sim.EdwardsLadder

open X25519Sim.LadderMath X25519Sim.EdwardsBridge DalekSim DalekSim.Edwards

variable {F : Type*} [Field F]

/-- The projective Montgomery point `(1 + y : 1 - y)` of the Edwards point `(x, y)`. -/
def rep (P : F × F) : Pt F := (1 + P.2, 1 - P.2)

/-- The encoding of `rep P` is `toU` of the y-coordinate. -/
theorem enc_rep (P : F × F) : enc (rep P) = toU P.2 := rfl

/-- If `a (1 - y) = b (1 + y)`, then `(a, b)` is `(1 + y, 1 - y)` times `(a + b) / 2`. -/
theorem smul_of_cross {a b y : F} (h2 : (2 : F) ≠ 0) (h : a * (1 - y) = b * (1 + y)) :
    ((a, b) : Pt F) = smul ((a + b) / 2) (1 + y, 1 - y) := by
  simp only [smul, Prod.mk.injEq]
  constructor
  · field_simp; linear_combination h
  · field_simp; linear_combination -h

/-- **Doubling.** For every point `P` on the curve, `dbl (rep P)` is `rep (P + P)` times a
nonzero factor. -/
theorem dbl_rep {d : F} [Complete d] (hd' : 121666 * d = -121665) {P : F × F}
    (hP : OnCurve d P) : ∃ c : F, c ≠ 0 ∧ dbl (rep P) = smul c (rep (add d P P)) := by
  have hs := one_sub_ne_zero hP hP
  obtain ⟨x, y⟩ := P
  simp only [OnCurve] at hP hs
  have h2 : (2 : F) ≠ 0 := Complete.two_ne_zero (d := d)
  have hk := dbl_key hd' hP
  have hK := dbl_factor_ne_zero hd' hP
  refine ⟨8 * (1 + 121665 * (1 - y ^ 2)) * (1 - d * x * x * y * y),
    mul_ne_zero (mul_ne_zero (by
      rw [show (8 : F) = 2 ^ 3 by norm_num]; exact pow_ne_zero _ h2) hK) hs, ?_⟩
  simp only [dbl, rep, smul, add, Prod.mk.injEq]
  generalize hsd : 1 - d * x * x * y * y = s at *
  constructor
  · field_simp
    linear_combination -16 * hk + 8 * (1 + 121665 * (1 - y ^ 2)) * (hsd - hP)
  · field_simp
    linear_combination 8 * (1 + 121665 * (1 - y ^ 2)) * (hsd - hP)

/-- **Differential addition.** Let `y_D` be the y-coordinate of `P - Q = add d P (-Q.1, Q.2)`.
If `u (1 - y_D) = 1 + y_D` and `u ≠ 0`, then `dadd u (rep P) (rep Q)` is `rep (P + Q)` times a
nonzero factor. The hypotheses exclude `P = Q` and `P - Q = (0, -1)`. -/
theorem dadd_rep {d : F} [Complete d] {P Q : F × F} (hP : OnCurve d P) (hQ : OnCurve d Q)
    {u : F} (hu : u * (1 - (add d P (-Q.1, Q.2)).2) = 1 + (add d P (-Q.1, Q.2)).2)
    (hu0 : u ≠ 0) : ∃ c : F, c ≠ 0 ∧ dadd u (rep P) (rep Q) = smul c (rep (add d P Q)) := by
  have h2 : (2 : F) ≠ 0 := Complete.two_ne_zero (d := d)
  have hQ' : OnCurve d (-Q.1, Q.2) := by simpa [OnCurve] using hQ
  have p1 := one_sub_ne_zero hP hQ
  have m1 := one_sub_ne_zero hP hQ'
  have E3 : (add d P Q).2 * (1 - d * P.1 * Q.1 * P.2 * Q.2) = P.2 * Q.2 + P.1 * Q.1 :=
    div_mul_cancel₀ _ p1
  have ED : (add d P (-Q.1, Q.2)).2 * (1 - d * P.1 * (-Q.1) * P.2 * Q.2) =
      P.2 * Q.2 + P.1 * (-Q.1) :=
    div_mul_cancel₀ _ m1
  simp only [rep]
  generalize (add d P Q).2 = y3 at *
  generalize (add d P (-Q.1, Q.2)).2 = yD at *
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  simp only [OnCurve] at hP hQ p1 m1 E3 ED ⊢
  have core := dadd_core d x1 y1 x2 y2 hP hQ
  set t := d * x1 * x2 * y1 * y2 with ht
  set s3 := y1 * y2 + x1 * x2 with hs3
  have hD := one_sub_ne_zero_of_u h2 hu
  have m1' : 1 + d * x1 * x2 * y1 * y2 ≠ 0 := by
    intro h; apply m1; linear_combination h
  have key : (1 - yD) * (1 - d * x1 * x2 * y1 * y2) * (1 + d * x1 * x2 * y1 * y2) *
      (16 * (y1 + y2) ^ 2 * (1 - y3) - 16 * u * (y1 - y2) ^ 2 * (1 + y3)) = 0 := by
    linear_combination 16 * (-core - (y1 + y2) ^ 2 * ((1 - yD) * (1 + t) * E3 + (1 - t - s3) * ED) -
      (y1 - y2) ^ 2 * ((1 - t) * (1 + t) * (1 + y3) * hu + (1 + t) * (1 + yD) * E3 +
        (1 - t + s3) * ED))
  have cross : 16 * (y1 + y2) ^ 2 * (1 - y3) = 16 * u * (y1 - y2) ^ 2 * (1 + y3) := by
    have := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero hD p1) m1')
    linear_combination this
  have hdadd : dadd u (1 + y1, 1 - y1) (1 + y2, 1 - y2) =
      (16 * (y1 + y2) ^ 2, 16 * u * (y1 - y2) ^ 2) := by
    simp only [dadd, Prod.mk.injEq]; constructor <;> ring
  rw [hdadd, smul_of_cross h2 cross]
  refine ⟨_, ?_, rfl⟩
  intro hc
  -- `c = 0` forces `y₁ = y₂ = 0`, then `P - Q = (0, -1)` and `u = 0`.
  have hab : (16 : F) * (y1 + y2) ^ 2 + 16 * u * (y1 - y2) ^ 2 = 0 := by
    rw [div_eq_zero_iff] at hc; exact hc.resolve_right h2
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2
  have ha : 2 * (16 * (y1 + y2) ^ 2) = 0 := by linear_combination cross + (1 + y3) * hab
  have hs : y1 + y2 = 0 := by simpa [h2, h16] using ha
  have hb : u * (y1 - y2) ^ 2 = 0 := by
    have : 16 * (u * (y1 - y2) ^ 2) = 0 := by linear_combination hab - 16 * (y1 + y2) * hs
    simpa [h16] using this
  have hd0 : y1 - y2 = 0 := by simpa [hu0] using hb
  have hy1 : y1 = 0 := by
    have : 2 * y1 = 0 := by linear_combination hs + hd0
    simpa [h2] using this
  have hy2 : y2 = 0 := by linear_combination hs - hy1
  subst hy1 hy2
  have hm : yD ^ 2 = 1 := by
    have e : yD = -(x1 * x2) := by simpa using ED
    rw [e]; linear_combination -x2 ^ 2 * hP + hQ
  have h1 : (1 + yD) ^ 2 = 0 := by linear_combination -(1 + yD) * hu - u * hm
  have h1' : 1 + yD = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  apply hu0
  have : 2 * u = 0 := by linear_combination hu + (1 + u) * h1'
  simpa [h2] using this

/-! ## The ladder on multiples of a point -/

/-- The number read from `bits`, most significant first, after the bits before them gave `n`. -/
def bitsVal (n : ℕ) (bits : List Bool) : ℕ := bits.foldl (fun n b => 2 * n + b.toNat) n

/-- No bits: the number stays `n`. -/
@[simp] theorem bitsVal_nil (n : ℕ) : bitsVal n [] = n := rfl

/-- One bit `b` turns `n` into `2 n + b`. -/
theorem bitsVal_cons (n : ℕ) (b : Bool) (bits : List Bool) :
    bitsVal n (b :: bits) = bitsVal (2 * n + b.toNat) bits := rfl

section Ladder

variable {d : F} [Complete d] (hd' : 121666 * d = -121665) (B : Point d) {u : F}
  (hB : u * (1 - B.1.2) = 1 + B.1.2) (hu0 : u ≠ 0)
include hd' hB hu0

omit hd' in
/-- The ladder's differential addition of `n • B` and `(n + 1) • B` gives `(2 n + 1) • B`. -/
theorem dadd_rep_nsmul (n : ℕ) : ∃ c : F, c ≠ 0 ∧
    dadd u (rep (n • B).1) (rep ((n + 1) • B).1) = smul c (rep ((2 * n + 1) • B).1) := by
  have hD : add d (n • B).1 (-((n + 1) • B).1.1, ((n + 1) • B).1.2) = (-B).1 := by
    rw [← Point.val_neg, ← Point.val_add]
    congr 1
    rw [succ_nsmul]; abel
  have hu : u * (1 - (add d (n • B).1 (-((n + 1) • B).1.1, ((n + 1) • B).1.2)).2) =
      1 + (add d (n • B).1 (-((n + 1) • B).1.1, ((n + 1) • B).1.2)).2 := by
    rw [hD]; exact hB
  obtain ⟨c, hc, h⟩ := dadd_rep (n • B).2 ((n + 1) • B).2 hu hu0
  refine ⟨c, hc, ?_⟩
  rw [h, Point.val_two_mul_add_one_nsmul, Edwards.add_comm']

omit hB hu0 in
/-- The ladder's doubling of `n • B` gives `(2 n) • B`. -/
theorem dbl_rep_nsmul (n : ℕ) : ∃ c : F, c ≠ 0 ∧
    dbl (rep (n • B).1) = smul c (rep ((2 * n) • B).1) := by
  obtain ⟨c, hc, h⟩ := dbl_rep hd' (n • B).2
  exact ⟨c, hc, by rw [h, Point.val_two_mul_nsmul]⟩

/-- **The ladder invariant.** Let `121666 d = -121665`, `u (1 - B.y) = 1 + B.y` and `u ≠ 0`. If
the state holds `n • B` and `(n + 1) • B` up to nonzero factors, then after `bits` it holds
`m • B` and `(m + 1) • B` up to nonzero factors, with `m = bitsVal n bits`. -/
theorem ladder_rep (bits : List Bool) (n : ℕ) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ a' b' : F, a' ≠ 0 ∧ b' ≠ 0 ∧
      ladder u bits (smul a (rep (n • B).1), smul b (rep ((n + 1) • B).1)) =
        (smul a' (rep (bitsVal n bits • B).1), smul b' (rep ((bitsVal n bits + 1) • B).1)) := by
  induction bits generalizing n a b with
  | nil => exact ⟨a, b, ha, hb, rfl⟩
  | cons bit bits ih =>
    rw [ladder_cons, bitsVal_cons]
    cases bit
    · obtain ⟨c, hc, hdb⟩ := dbl_rep_nsmul hd' B n
      obtain ⟨e, he, hda⟩ := dadd_rep_nsmul B hB hu0 n
      have hs : lstep u false (smul a (rep (n • B).1), smul b (rep ((n + 1) • B).1)) =
          (smul (a ^ 4 * c) (rep ((2 * n) • B).1), smul ((a * b) ^ 2 * e)
            (rep ((2 * n + 1) • B).1)) := by
        simp only [lstep, cswap, pad, Bool.false_eq_true, if_false, dbl_smul, dadd_smul, hdb,
          hda, smul_smul']
      rw [hs, Bool.toNat_false, add_zero]
      exact ih _ _ _ (mul_ne_zero (pow_ne_zero _ ha) hc)
        (mul_ne_zero (pow_ne_zero _ (mul_ne_zero ha hb)) he)
    · obtain ⟨c, hc, hdb⟩ := dbl_rep_nsmul hd' B (n + 1)
      obtain ⟨e, he, hda⟩ := dadd_rep_nsmul B hB hu0 n
      have hs : lstep u true (smul a (rep (n • B).1), smul b (rep ((n + 1) • B).1)) =
          (smul ((a * b) ^ 2 * e) (rep ((2 * n + 1) • B).1),
            smul (b ^ 4 * c) (rep ((2 * n + 1 + 1) • B).1)) := by
        rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
        simp only [lstep, cswap, pad, if_true, dbl_smul, dadd_smul', hdb, dadd_comm u
          (rep ((n + 1) • B).1), hda, smul_smul']
      rw [hs, Bool.toNat_true]
      exact ih _ _ _ (mul_ne_zero (pow_ne_zero _ (mul_ne_zero ha hb)) he)
        (mul_ne_zero (pow_ne_zero _ hb) hc)

/-- **The ladder computes `toU (m • B)`.** Let `121666 d = -121665`, `u (1 - B.y) = 1 + B.y`
and `u ≠ 0`. From the start state `((1 : 0), (u : 1))`, the first point of the ladder over
`bits` encodes `toU (m • B)`, with `m = bitsVal 0 bits`. -/
theorem enc_ladder (bits : List Bool) :
    enc (ladder u bits ((1, 0), (u, 1))).1 = toU (bitsVal 0 bits • B).1.2 := by
  have h2 : (2 : F) ≠ 0 := Complete.two_ne_zero (d := d)
  have hB1 := one_sub_ne_zero_of_u h2 hB
  have hstart : (((1 : F), (0 : F)), (u, (1 : F))) =
      (smul 2⁻¹ (rep ((0 : ℕ) • B).1), smul (1 - B.1.2)⁻¹ (rep (((0 : ℕ) + 1) • B).1)) := by
    simp only [zero_nsmul, zero_add, one_nsmul, Point.val_zero, rep, smul, Prod.mk.injEq]
    refine ⟨⟨?_, by ring⟩, ?_, ?_⟩
    · field_simp; norm_num
    · field_simp; linear_combination hB
    · field_simp
  obtain ⟨a, b, ha, _, h⟩ := ladder_rep hd' B hB hu0 bits 0 _ _ (inv_ne_zero h2)
    (inv_ne_zero hB1)
  rw [hstart, h, enc_smul _ ha, enc_rep]

end Ladder

/-! ## edwards25519 -/

section Curve25519

/-- The base point `B` of edwards25519 (RFC 8032, section 5.1): `y = 4 / 5`, and the canonical
representative of `x` is even. -/
def basePoint : Point dEd :=
  ⟨(15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960), by
    unfold OnCurve dEd d p; decide +kernel⟩

/-- `y = 4 / 5`: `5 y = 4`. -/
theorem basePoint_y : 5 * basePoint.1.2 = 4 := by
  unfold basePoint p; decide +kernel

/-- The canonical representative of `x` is even. -/
theorem basePoint_x_even : basePoint.1.1.val % 2 = 0 := by
  unfold basePoint p; decide +kernel

/-- `B` maps to `u = 9`: `9 (1 - y) = 1 + y`. -/
theorem basePoint_u : (9 : ZMod p) * (1 - basePoint.1.2) = 1 + basePoint.1.2 := by
  unfold basePoint p; decide +kernel

/-- `toU y = 9` for the base point. -/
theorem toU_basePoint : toU basePoint.1.2 = 9 := by
  have h : (1 : ZMod p) - basePoint.1.2 ≠ 0 := by
    unfold basePoint p; decide +kernel
  rw [toU, ← basePoint_u, mul_assoc, mul_inv_cancel₀ h, mul_one]

/-- `9 ≠ 0` in `ZMod p`. -/
theorem nine_ne_zero : (9 : ZMod p) ≠ 0 := by
  unfold p; decide +kernel

/-- **The ladder at `u = 9` computes `toU (m • B)`** on edwards25519, where `m` is the number
with the bits `bits`, most significant first. -/
theorem enc_ladder_nine (bits : List Bool) :
    enc (ladder (9 : ZMod p) bits ((1, 0), (9, 1))).1 = toU (bitsVal 0 bits • basePoint).1.2 :=
  enc_ladder dEd_rel basePoint basePoint_u nine_ne_zero bits

end Curve25519

end X25519Sim.EdwardsLadder
