import Sim.Decode

/-! # `compress` against the reference `encode`

Both compute `u1 = (Z + Y)(Z - Y)`, `u2 = X Y`, the inverse square root of `u1 u2²`, then
rotate the point by `√-1` if `T / Z` is negative, fix the sign of `y` and take the
nonnegative `s`. The proof goes call by call. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace RistrettoSim

/-- `1/sqrt(a - d)` in the reference field. -/
def zInvAD : _root_.field.Fe := ((nInvsqrtAMinusD : Nat) : _root_.field.Fe)

/-- The value that `encode` writes as bytes, for the inverse square root `I`. `u1`, `u2`,
`zinv` and `rot` are intermediate values of `encode`, passed as arguments so that the
statement stays small. -/
def encTail (X Y Z u1 u2 I zinv : _root_.field.Fe) (rot : Prop) [Decidable rot] :
    _root_.field.Fe :=
  let x := if rot then Y * zI else X
  let y := if rot then X * zI else Y
  let den := if rot then I * u1 * zInvAD else I * u2
  absZ (den * (Z - (if negP (x * zinv) then -y else y)))

/-- `u1` of encoding. -/
def encU1 (Y Z : _root_.field.Fe) : _root_.field.Fe := (Z + Y) * (Z - Y)

/-- The `z_inv` of `encode`, for the inverse square root `I`: `(I u1) (I u2) T`. -/
def encZinv (X Y Z T I : _root_.field.Fe) : _root_.field.Fe := I * encU1 Y Z * (I * (X * Y)) * T

/-- The value that `encode` writes as bytes. -/
def encS (X Y Z T I : _root_.field.Fe) : _root_.field.Fe :=
  encTail X Y Z (encU1 Y Z) (X * Y) I (encZinv X Y Z T I) (negP (T * encZinv X Y Z T I))

/-- The control flow of `encode` after the inverse square root. -/
theorem encode_tail (X Y Z u1 u2 I zinv T : _root_.field.Fe) :
    (do
      let x ← if decide (negP (T * zinv)) = true then ok (Y * zI) else ok X
      let y ← if decide (negP (T * zinv)) = true then ok (X * zI) else ok Y
      let den ← if decide (negP (T * zinv)) = true then ok (I * u1 * zInvAD) else ok (I * u2)
      let y1 ← if decide (negP (x * zinv)) = true then ok (-y) else ok y
      let s ← ristretto_ref.abs (den * (Z - y1))
      _root_.field.fe_to_bytes s) =
    _root_.field.fe_to_bytes (encTail X Y Z u1 u2 I zinv (negP (T * zinv))) := by
  unfold encTail
  by_cases hr : negP (T * zinv)
  · simp only [hr, decide_true, if_true, bind_ok]
    by_cases hy : negP (Y * zI * zinv)
    · simp only [hy, decide_true, if_true, bind_ok, ref_abs]
    · simp only [hy, decide_false, Bool.false_eq_true, if_false, bind_ok, ref_abs]
  · simp only [hr, decide_false, Bool.false_eq_true, if_false, bind_ok]
    by_cases hy : negP (X * zinv)
    · simp only [hy, decide_true, if_true, bind_ok, ref_abs]
    · simp only [hy, decide_false, Bool.false_eq_true, if_false, bind_ok, ref_abs]

/-- `encode` on a tuple. The `let` pattern of the generated code does not reduce under `simp`,
so this lemma restates the body, by `rfl`. -/
theorem encode_tuple (X Y Z T : _root_.field.Fe) :
    ristretto_ref.encode (X, Y, Z, T) = (do
    let f ← _root_.field.fe_add Z Y
    let f1 ← _root_.field.fe_sub Z Y
    let u1 ← _root_.field.fe_mul f f1
    let u2 ← _root_.field.fe_mul X Y
    let f2 ← _root_.field.fe_lit 1#u32
    let f3 ← _root_.field.fe_sq u2
    let f4 ← _root_.field.fe_mul u1 f3
    let (_, invsqrt) ← ristretto_ref.sqrt_ratio_m1 f2 f4
    let den1 ← _root_.field.fe_mul invsqrt u1
    let den2 ← _root_.field.fe_mul invsqrt u2
    let f5 ← _root_.field.fe_mul den1 den2
    let z_inv ← _root_.field.fe_mul f5 T
    let f6 ← ristretto_ref.sqrt_m1
    let iX ← _root_.field.fe_mul X f6
    let iY ← _root_.field.fe_mul Y f6
    let f7 ← ristretto_ref.invsqrt_a_minus_d
    let enchanted_denominator ← _root_.field.fe_mul den1 f7
    let f8 ← _root_.field.fe_mul T z_inv
    let rotate ← ristretto_ref.is_negative f8
    let x ← ristretto_ref.select iY rotate X
    let y ← ristretto_ref.select iX rotate Y
    let den_inv ← ristretto_ref.select enchanted_denominator rotate den2
    let f9 ← ristretto_ref.neg_fe y
    let f10 ← _root_.field.fe_mul x z_inv
    let b ← ristretto_ref.is_negative f10
    let y1 ← ristretto_ref.select f9 b y
    let f11 ← _root_.field.fe_sub Z y1
    let f12 ← _root_.field.fe_mul den_inv f11
    let s ← ristretto_ref.abs f12
    _root_.field.fe_to_bytes s) := rfl

/-- The reference `encode` in closed form. -/
theorem ref_encode_eq (X Y Z T I : _root_.field.Fe) (b : Bool)
    (hI : ristretto_ref.sqrt_ratio_m1 1 (encU1 Y Z * (X * Y) ^ 2) = ok (b, I)) :
    ristretto_ref.encode (X, Y, Z, T) = _root_.field.fe_to_bytes (encS X Y Z T I) := by
  rw [encode_tuple]
  unfold ristretto_ref.select ristretto_ref.neg_fe
  simp only [_root_.field.fe_sq, _root_.field.fe_mul, _root_.field.fe_sub, _root_.field.fe_add,
    _root_.field.fe_lit, ref_lit_one, ref_sqrt_m1, ref_invsqrt_a_minus_d, ref_zero_sub, bind_ok]
  rw [show (Z + Y) * (Z - Y) = encU1 Y Z from rfl, hI, bind_ok]
  simp only [uncurry_apply_pair, ref_is_negative, bind_ok]
  rw [show ((nSqrtM1 : Nat) : _root_.field.Fe) = zI from rfl,
    show ((nInvsqrtAMinusD : Nat) : _root_.field.Fe) = zInvAD from rfl,
    show I * encU1 Y Z * (I * (X * Y)) * T = encZinv X Y Z T I from rfl]
  exact encode_tail X Y Z (encU1 Y Z) (X * Y) I (encZinv X Y Z T I) T

/-! ## The encoding theorem -/

/-- `conditional_assign` under `toZ`, with the choice named by a proposition. -/
theorem sel_z (a b r : FE) (c : subtle.Choice) (P : Prop) [Decidable P]
    (hc : c.val = 1#u8 ↔ P) (hr : r = if c.val = 1#u8 then b else a) :
    toZ r = if P then toZ b else toZ a := by
  rw [hr]
  by_cases h : c.val = 1#u8
  · rw [if_pos h, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]

/-- `conditional_assign` keeps a limb bound that both inputs have. -/
theorem bnd_sel {k : Nat} (a b r : FE) (c : subtle.Choice) (ha : Bnd k a) (hb : Bnd k b)
    (hr : r = if c.val = 1#u8 then b else a) : Bnd k r := by
  rw [hr]; split <;> assumption

/-- Encoding refines the reference. If every limb of the four coordinates of `P` is below
`2 ^ 53`, `compress P` returns without panic, overflow or divergence, and the reference
`encode` returns the same bytes on the four coordinates under `toZ`. `P` does not need to be
on the curve. -/
theorem compress_refines (P : ristretto.RistrettoPoint) (hP : BndPt 53 P) :
    ristretto.RistrettoPoint.compress P ⦃ c =>
      ristretto_ref.encode (toZPt P) = ok c ⦄ := by
  obtain ⟨bX, bY, bZ, bT⟩ := hP
  unfold ristretto.RistrettoPoint.compress
  step with add_z as ⟨zpy, hzpy, bzpy⟩
  step with sub_z as ⟨zmy, hzmy, bzmy⟩
  · exact bnd_mono bZ (by norm_num)
  · exact bnd_mono bY (by norm_num)
  step with mul_z as ⟨u1, hu1, bu1⟩
  · exact bnd_mono bzmy (by norm_num)
  step with mul_z as ⟨u2, hu2, bu2⟩
  · exact bnd_mono bX (by norm_num)
  · exact bnd_mono bY (by norm_num)
  step with square_z as ⟨u2s, hu2s, bu2s⟩
  · exact bnd_mono bu2 (by norm_num)
  step with mul_z as ⟨w, hw, bw⟩
  · exact bnd_mono bu1 (by norm_num)
  · exact bnd_mono bu2s (by norm_num)
  step with invsqrt_refines as ⟨ok1, I, ws, hws, _, bI⟩
  · exact bnd_mono bw (by norm_num)
  step with mul_z as ⟨i1, hi1, bi1⟩
  · exact bnd_mono bI (by norm_num)
  · exact bnd_mono bu1 (by norm_num)
  step with mul_z as ⟨i2, hi2, bi2⟩
  · exact bnd_mono bI (by norm_num)
  · exact bnd_mono bu2 (by norm_num)
  step with mul_z as ⟨i2T, hi2T, bi2T⟩
  · exact bnd_mono bi2 (by norm_num)
  · exact bnd_mono bT (by norm_num)
  step with mul_z as ⟨zinv, hzinv, bzinv⟩
  · exact bnd_mono bi1 (by norm_num)
  · exact bnd_mono bi2T (by norm_num)
  step with sqrt_m1_spec as ⟨fe, hfe, bfe⟩
  step with mul_z as ⟨iX, hiX, biX⟩
  · exact bnd_mono bX (by norm_num)
  · exact bnd_mono bfe (by norm_num)
  step with mul_z as ⟨iY, hiY, biY⟩
  · exact bnd_mono bY (by norm_num)
  · exact bnd_mono bfe (by norm_num)
  step with invsqrt_a_minus_d_spec as ⟨fe1, hfe1, bfe1⟩
  step with mul_z as ⟨ench, hench, bench⟩
  · exact bnd_mono bi1 (by norm_num)
  · exact bnd_mono bfe1 (by norm_num)
  step with mul_z as ⟨tz, htz, btz⟩
  · exact bnd_mono bT (by norm_num)
  · exact bnd_mono bzinv (by norm_num)
  step with is_negative_z as ⟨rot, hrot⟩
  step with conditional_assign_eq as ⟨X1, hX1⟩
  step with conditional_assign_eq as ⟨Y1, hY1⟩
  step with conditional_assign_eq as ⟨i21, hi21⟩
  have bX1 : Bnd 53 X1 := bnd_sel _ _ _ _ bX (bnd_mono biY (by norm_num)) hX1
  have bY1 : Bnd 53 Y1 := bnd_sel _ _ _ _ bY (bnd_mono biX (by norm_num)) hY1
  have bi21 : Bnd 52 i21 := bnd_sel _ _ _ _ bi2 bench hi21
  step with mul_z as ⟨xz, hxz, bxz⟩
  · exact bnd_mono bX1 (by norm_num)
  · exact bnd_mono bzinv (by norm_num)
  step with is_negative_z as ⟨ys, hys⟩
  step with neg_z as ⟨yneg, hyneg, byneg⟩
  · exact bnd_mono bY1 (by norm_num)
  step with conditional_assign_eq as ⟨Y2, hY2⟩
  have bY2 : Bnd 53 Y2 := bnd_sel _ _ _ _ bY1 (bnd_mono byneg (by norm_num)) hY2
  step with sub_z as ⟨zmy2, hzmy2, bzmy2⟩
  · exact bnd_mono bZ (by norm_num)
  · exact bnd_mono bY2 (by norm_num)
  step with mul_z as ⟨s, hs, bs⟩
  · exact bnd_mono bi21 (by norm_num)
  · exact bnd_mono bzmy2 (by norm_num)
  step with is_negative_z as ⟨sn, hsn⟩
  step with neg_z as ⟨sneg, hsneg, bsneg⟩
  · exact bnd_mono bs (by norm_num)
  step with conditional_assign_eq as ⟨s1, hs1⟩
  step with to_bytes_val as ⟨a, ha⟩
  -- the reference side
  have hu1' : toZ u1 = encU1 (toZ P.Y) (toZ P.Z) := by rw [hu1, hzpy, hzmy]; rfl
  have hw' : toZ w = encU1 (toZ P.Y) (toZ P.Z) * (toZ P.X * toZ P.Y) ^ 2 := by
    rw [hw, hu1', hu2s, hu2]
  rw [hw'] at hws
  -- the real values, in the reference's terms
  have hI : toZ fe = zI := hfe
  have hAD : toZ fe1 = zInvAD := hfe1
  have hz : toZ zinv = encZinv (toZ P.X) (toZ P.Y) (toZ P.Z) (toZ P.T) (toZ I) := by
    rw [hzinv, hi1, hi2T, hi2, hu1', hu2]; unfold encZinv; ring
  have hrot' : rot.val = 1#u8 ↔
      negP (toZ P.T * encZinv (toZ P.X) (toZ P.Y) (toZ P.Z) (toZ P.T) (toZ I)) := by
    rw [hrot, htz, hz]; rfl
  have hX1' := sel_z _ _ _ _ _ hrot' hX1
  have hY1' := sel_z _ _ _ _ _ hrot' hY1
  have hi21' := sel_z _ _ _ _ _ hrot' hi21
  have hys' : ys.val = 1#u8 ↔ negP (toZ X1 *
      encZinv (toZ P.X) (toZ P.Y) (toZ P.Z) (toZ P.T) (toZ I)) := by
    rw [hys, hxz, hz]; rfl
  have hY2' := sel_z _ _ _ _ _ hys' hY2
  have hs1' : toZ s1 = absZ (toZ s) := abs_of_select s sneg s1 sn hsn hsneg hs1
  have key : toZ s1 = encS (toZ P.X) (toZ P.Y) (toZ P.Z) (toZ P.T) (toZ I) := by
    rw [hs1', hs, hi21', hzmy2, hY2', hyneg, hX1', hY1', hench, hi1, hi2, hiX, hiY, hI, hAD,
      hu1', hu2]
    rfl
  unfold toZPt
  rw [ref_encode_eq _ _ _ _ _ ws hws]
  apply fe_to_bytes_eq
  rw [ha, key]

/-- Decoding followed by encoding. For every input, `decompress` is related to `decode` as in
`decompress_refines`. If it returns a point, `compress` of that point returns the bytes that
`encode` returns for the point of `decode`. -/
theorem decompress_compress_refines (b : Array U8 32#usize) :
    ristretto.CompressedRistretto.decompress b ⦃ r =>
      ∃ q, ristretto_ref.decode b = ok q ∧ DecRel q r ∧
        ∀ P, r = some P → ristretto.RistrettoPoint.compress P ⦃ c =>
          ∃ q', q = .Ok q' ∧ ristretto_ref.encode q' = ok c ⦄ ⦄ := by
  apply spec_mono (decompress_refines b)
  rintro r ⟨q, hq, hrel⟩
  refine ⟨q, hq, hrel, ?_⟩
  rintro P rfl
  match q, hrel with
  | .Ok q', ⟨hq', bX, bY, bZ, bT⟩ =>
    apply spec_mono (compress_refines P
      ⟨bnd_mono bX (by norm_num), bnd_mono bY (by norm_num), bnd_mono bZ (by norm_num),
        bnd_mono bT (by norm_num)⟩)
    intro c hc
    exact ⟨q', rfl, by rw [hq']; exact hc⟩

end RistrettoSim
