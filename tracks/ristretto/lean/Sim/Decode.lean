import Sim.SqrtRatio
import Sim.GeqP
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes

/-! # `decompress` against the reference `decode`

`step_1` reads `s` and tests that the encoding is canonical and that `s` is nonnegative.
`step_2` computes the point. Both are related to the reference `decode` call by call. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

namespace RistrettoSim

open DalekSim

/-- The value of `p`. -/
theorem p_val : p = 2 ^ 255 - 19 := rfl

/-- `step_1` reads the low 255 bits of the input, and the encoding test holds iff the input is
below `p`. -/
theorem step_1_z (b : Array U8 32#usize) :
    ristretto.decompress.step_1 b ⦃ r =>
      (r.1.val = 1#u8 ↔ U8x32_as_Nat b < p) ∧
      (r.2.1.val = 1#u8 ↔ (toZ r.2.2).val % 2 = 1) ∧
      toZ r.2.2 = ((U8x32_as_Nat b % 2 ^ 255 : Nat) : ZMod p) ∧ Bnd 51 r.2.2 ⦄ := by
  unfold ristretto.decompress.step_1 ristretto.CompressedRistretto.as_bytes
  simp only [lift, bind_ok]
  step with backend.serial.u64.field.FieldElement51.from_bytes_spec as ⟨s, hs, bs⟩
  step with to_bytes_val as ⟨sb, hsb⟩
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index,
    bind_ok]
  apply spec_bind (slice_ct_eq_arr sb b)
  intro cc hcc
  apply spec_bind (is_negative_z s)
  intro cn hcn
  rw [spec_ok]
  have hsz : toZ s = ((U8x32_as_Nat b % 2 ^ 255 : Nat) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hs
  refine ⟨?_, hcn, hsz, bs⟩
  rw [hcc]
  constructor
  · rintro rfl
    rw [hsb]
    exact ZMod.val_lt _
  · intro hlt
    apply U8x32_inj
    have h255 : U8x32_as_Nat b < 2 ^ 255 := lt_of_lt_of_le hlt (by rw [p_val]; omega)
    rw [hsb, hsz, Nat.mod_eq_of_lt h255]
    exact ZMod.val_natCast_of_lt hlt

/-- `invsqrt x` is `sqrt_ratio_i 1 x`. -/
theorem invsqrt_refines (x : FE) (hx : Bnd 54 x) :
    field.FieldElement51.invsqrt x ⦃ r =>
      ∃ b, ristretto_ref.sqrt_ratio_m1 1 (toZ x) = ok (b, toZ r.2) ∧
        (b = true ↔ r.1.val = 1#u8) ∧ Bnd 52 r.2 ⦄ := by
  unfold field.FieldElement51.invsqrt
  step with one_spec as ⟨one, hone, bone⟩
  apply spec_mono (sqrt_ratio_i_refines one x (bnd_mono bone (by norm_num)) hx)
  intro r hr
  rw [hone] at hr
  exact hr

/-- `d` in the reference field. -/
def zD : _root_.field.Fe := ((nD : Nat) : _root_.field.Fe)

/-- The `v` of decoding: `-(d (1 - S²)²) - (1 + S²)²`. -/
def decV (S : _root_.field.Fe) : _root_.field.Fe := -(zD * (1 - S ^ 2) ^ 2) - (1 + S ^ 2) ^ 2
/-- The `x` of decoding, for the root `I`: `|2 S I (1 + S²)|`. -/
def decX (S I : _root_.field.Fe) : _root_.field.Fe := absZ ((S + S) * (I * (1 + S ^ 2)))
/-- The `y` of decoding, for the root `I`: `(1 - S²) I² (1 + S²) v`. -/
def decY (S I : _root_.field.Fe) : _root_.field.Fe := (1 - S ^ 2) * (I * (I * (1 + S ^ 2)) * decV S)

/-- `conditional_assign(x, -x, is_negative x)` is `absZ`. -/
theorem abs_of_select (x xn r : FE) (c : subtle.Choice)
    (hc : c.val = 1#u8 ↔ (toZ x).val % 2 = 1) (hxn : toZ xn = - toZ x)
    (hr : r = if c.val = 1#u8 then xn else x) : toZ r = absZ (toZ x) := by
  rw [hr]; unfold absZ negP
  by_cases h : c.val = 1#u8
  · rw [if_pos h, hxn, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]

/-- If the limbs of `s` are below `2 ^ 51`, `step_2 s` returns without failure. With `S = toZ s`
and `(ws, I)` the result of the reference `sqrt_ratio_m1 1 (decV S (1 + S²)²)`: the first
`Choice` is 1 iff `ws`, the point is `(decX S I, decY S I, 1, decX S I · decY S I)` under
`toZ`, the second `Choice` is 1 iff `T` is odd, and the third is 1 iff `Y = 0`. All limbs
are below `2 ^ 52`. -/
theorem step_2_z (s : FE) (hs : Bnd 51 s) :
    ristretto.decompress.step_2 s ⦃ r =>
      ∃ ws I, ristretto_ref.sqrt_ratio_m1 1 (decV (toZ s) * (1 + toZ s ^ 2) ^ 2) = ok (ws, I) ∧
        (ws = true ↔ r.1.val = 1#u8) ∧
        toZ r.2.2.2.X = decX (toZ s) I ∧
        toZ r.2.2.2.Y = decY (toZ s) I ∧
        toZ r.2.2.2.Z = 1 ∧
        toZ r.2.2.2.T = toZ r.2.2.2.X * toZ r.2.2.2.Y ∧
        (r.2.1.val = 1#u8 ↔ (toZ r.2.2.2.T).val % 2 = 1) ∧
        (r.2.2.1.val = 1#u8 ↔ toZ r.2.2.2.Y = 0) ∧
        Bnd 52 r.2.2.2.X ∧ Bnd 52 r.2.2.2.Y ∧ Bnd 52 r.2.2.2.Z ∧ Bnd 52 r.2.2.2.T ⦄ := by
  unfold ristretto.decompress.step_2
  step with one_spec as ⟨one, hone, bone⟩
  step with square_z as ⟨ss, hss, bss⟩
  · exact bnd_mono hs (by norm_num)
  step with sub_z as ⟨u1, hu1, bu1⟩
  · exact bnd_mono bone (by norm_num)
  · exact bnd_mono bss (by norm_num)
  step with add_z as ⟨u2, hu2, bu2⟩
  · exact bnd_mono bone (by norm_num)
  · exact bnd_mono bss (by norm_num)
  step with square_z as ⟨u2s, hu2s, bu2s⟩
  step with edwards_d_spec as ⟨fd, hfd, bfd⟩
  step with neg_z as ⟨nd, hnd, bnd⟩
  · exact bnd_mono bfd (by norm_num)
  step with square_z as ⟨u1s, hu1s, bu1s⟩
  · exact bnd_mono bu1 (by norm_num)
  step with mul_z as ⟨ndu, hndu, bndu⟩
  · exact bnd_mono bnd (by norm_num)
  · exact bnd_mono bu1s (by norm_num)
  step with sub_z as ⟨v, hv, bv⟩
  · exact bnd_mono bndu (by norm_num)
  · exact bnd_mono bu2s (by norm_num)
  step with mul_z as ⟨vu, hvu, bvu⟩
  · exact bnd_mono bv (by norm_num)
  · exact bnd_mono bu2s (by norm_num)
  step with invsqrt_refines as ⟨ok1, I, ws, hws, hwsiff, bI⟩
  · exact bnd_mono bvu (by norm_num)
  step with mul_z as ⟨Dx, hDx, bDx⟩
  · exact bnd_mono bI (by norm_num)
  step with mul_z as ⟨Dxv, hDxv, bDxv⟩
  · exact bnd_mono bDx (by norm_num)
  · exact bnd_mono bv (by norm_num)
  step with mul_z as ⟨Dy, hDy, bDy⟩
  · exact bnd_mono bI (by norm_num)
  · exact bnd_mono bDxv (by norm_num)
  step with add_z as ⟨sps, hsps, bsps⟩
  · exact bnd_mono hs (by norm_num)
  · exact bnd_mono hs (by norm_num)
  step with mul_z as ⟨x, hx, bx⟩
  · exact bnd_mono bDx (by norm_num)
  step with is_negative_z as ⟨xn, hxn⟩
  step with neg_z as ⟨xneg, hxneg, bxneg⟩
  · exact bnd_mono bx (by norm_num)
  step with conditional_assign_eq as ⟨x1, hx1⟩
  have bx1 : Bnd 52 x1 := by rw [hx1]; split <;> assumption
  step with mul_z as ⟨y, hy, by'⟩
  · exact bnd_mono bu1 (by norm_num)
  · exact bnd_mono bDy (by norm_num)
  step with mul_z as ⟨t, ht, bt⟩
  · exact bnd_mono bx1 (by norm_num)
  · exact bnd_mono by' (by norm_num)
  step with is_negative_z as ⟨tn, htn⟩
  step with is_zero_z as ⟨yz, hyz⟩
  have hfd' : toZ fd = zD := hfd
  have hv' : toZ v = decV (toZ s) := by
    rw [hv, hndu, hnd, hfd', hu1s, hu1, hu2s, hu2, hone, hss]; unfold decV; ring
  have hu2' : toZ u2 = 1 + toZ s ^ 2 := by rw [hu2, hone, hss]
  have hvu' : toZ vu = decV (toZ s) * (1 + toZ s ^ 2) ^ 2 := by
    rw [hvu, hv', hu2s, hu2']
  have hx' : toZ x = (toZ s + toZ s) * (toZ I * (1 + toZ s ^ 2)) := by
    rw [hx, hsps, hDx, hu2']
  refine ⟨ws, toZ I, by rw [← hvu']; exact hws, hwsiff, ?_, ?_, hone, ht, htn, hyz,
    bx1, by', bnd_mono bone (by norm_num), bt⟩
  · rw [abs_of_select x xneg x1 xn hxn hxneg hx1, hx']; rfl
  · rw [hy, hu1, hone, hss, hDy, hDxv, hDx, hu2', hv']; unfold decY; ring

/-! ## The decoding theorem -/

/-- A point in the reference: four field elements. -/
abbrev RefPt := _root_.field.Fe × _root_.field.Fe × _root_.field.Fe × _root_.field.Fe

/-- The four coordinates of a real point under `toZ`. -/
def toZPt (P : edwards.EdwardsPoint) : RefPt := (toZ P.X, toZ P.Y, toZ P.Z, toZ P.T)

/-- Every limb of the four coordinates is below `2 ^ k`. -/
def BndPt (k : Nat) (P : edwards.EdwardsPoint) : Prop :=
  Bnd k P.X ∧ Bnd k P.Y ∧ Bnd k P.Z ∧ Bnd k P.T

/-- The relation of decoding results: hacspec `Result<RistrettoPoint, u8>` against dalek
`Option<RistrettoPoint>`. -/
def DecRel : core.result.Result RefPt U8 → Option ristretto.RistrettoPoint → Prop
  | .Ok q, some P => q = toZPt P ∧ BndPt 52 P
  | .Err e, none => e = 20#u8
  | _, _ => False

/-- `!a` on choices. -/
theorem not_eq (a : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitNotChoice.not a =
      ok (if a.val = 1#u8 then cZero else cOne) := by
  unfold subtle.Choice.Insts.CoreOpsBitNotChoice.not
  split <;> rfl

/-- `bool::from(c)` is `c ≠ 0`. -/
theorem bool_from (c : subtle.Choice) :
    Bool.Insts.CoreConvertFromChoice.from c = ok (c.val != 0#u8) := rfl

/-- hacspec `fe(1)` is 1. -/
theorem ref_lit_one : ((((1#u32 : U32) : Nat) : _root_.field.Fe)) = 1 := by
  show (((1 : Nat) : _root_.field.Fe)) = 1
  exact Nat.cast_one

/-- hacspec `fe(0)` is 0. -/
theorem ref_lit_zero : ((((0#u32 : U32) : Nat) : _root_.field.Fe)) = 0 := by
  show (((0 : Nat) : _root_.field.Fe)) = 0
  exact Nat.cast_zero

/-- The reference `DECODING_ERROR` is 20. -/
theorem decode_err : ristretto_ref.DECODING_ERROR = 20#u8 := by
  unfold ristretto_ref.DECODING_ERROR; rfl

/-- The reference rejects a non-canonical encoding. -/
theorem ref_decode_noncanon (b : Array U8 32#usize) (h : ¬ U8x32_as_Nat b < p) :
    ristretto_ref.decode b = ok (core.result.Result.Err 20#u8) := by
  unfold ristretto_ref.decode
  have hge : decide (2 ^ 255 - 19 ≤ U8x32_as_Nat b) = true := by
    rw [decide_eq_true_iff]; rw [p_val] at h; omega
  rw [fe_from_bytes_eq, bind_ok, geq_p_eq, bind_ok, hge, if_pos rfl, decode_err]

/-- The reference rejects a negative `s`. -/
theorem ref_decode_neg (b : Array U8 32#usize) (h : U8x32_as_Nat b < p) (S : _root_.field.Fe)
    (hS : ((U8x32_as_Nat b : Nat) : _root_.field.Fe) = S)
    (hn : negP S) :
    ristretto_ref.decode b = ok (core.result.Result.Err 20#u8) := by
  unfold ristretto_ref.decode
  have hge : decide (2 ^ 255 - 19 ≤ U8x32_as_Nat b) = false := by
    rw [decide_eq_false_iff_not]; rw [p_val] at h; omega
  rw [fe_from_bytes_eq, bind_ok, geq_p_eq, bind_ok, hge, if_neg Bool.false_ne_true, hS,
    ref_is_negative, bind_ok, if_pos (decide_eq_true hn), decode_err]

/-- The result of decoding after the two tests on `s`. -/
def decRes (S I : _root_.field.Fe) (ws : Bool) : core.result.Result RefPt U8 :=
  if ws then
    if negP (decX S I * decY S I) then .Err 20#u8
    else if decY S I = 0 then .Err 20#u8
    else .Ok (decX S I, decY S I, 1, decX S I * decY S I)
  else .Err 20#u8

/-- The reference `decode` on a canonical, nonnegative encoding. -/
theorem ref_decode_main (b : Array U8 32#usize) (h : U8x32_as_Nat b < p) (S : _root_.field.Fe)
    (hS : ((U8x32_as_Nat b : Nat) : _root_.field.Fe) = S)
    (hn : ¬ negP S) (ws : Bool) (I : _root_.field.Fe)
    (hws : ristretto_ref.sqrt_ratio_m1 1 (decV S * (1 + S ^ 2) ^ 2) = ok (ws, I)) :
    ristretto_ref.decode b = ok (decRes S I ws) := by
  unfold ristretto_ref.decode
  have hge : decide (2 ^ 255 - 19 ≤ U8x32_as_Nat b) = false := by
    rw [decide_eq_false_iff_not]; rw [p_val] at h; omega
  rw [fe_from_bytes_eq, bind_ok, geq_p_eq, bind_ok, hge, if_neg Bool.false_ne_true, hS,
    ref_is_negative, bind_ok, if_neg (by simpa using hn)]
  unfold ristretto_ref.neg_fe ristretto_ref.eq
  simp only [_root_.field.fe_sq, _root_.field.fe_mul, _root_.field.fe_sub, _root_.field.fe_add,
    _root_.field.fe_lit, _root_.field.fe_eq, ref_d, ref_lit_one, ref_zero_sub, bind_ok]
  rw [show ((nD : Nat) : _root_.field.Fe) = zD from rfl,
    show (-(zD * (1 - S ^ 2) ^ 2) - (1 + S ^ 2) ^ 2) = decV S from rfl, hws, bind_ok]
  simp only [uncurry_apply_pair, ref_abs, bind_ok]
  rw [show absZ ((S + S) * (I * (1 + S ^ 2))) = decX S I from rfl,
    show (1 - S ^ 2) * (I * (I * (1 + S ^ 2)) * decV S) = decY S I from rfl, ref_lit_zero]
  unfold decRes
  cases ws
  · simp only [Bool.false_eq_true, if_false, decode_err]
  · simp only [if_true, ref_is_negative, bind_ok, decode_err]
    by_cases ht : negP (decX S I * decY S I)
    · rw [if_pos (decide_eq_true ht), if_pos ht]
    · rw [if_neg (by simpa using ht), if_neg ht]
      by_cases hy : decY S I = 0
      · rw [if_pos (decide_eq_true hy), if_pos hy]
      · rw [if_neg (by simpa using hy), if_neg hy]

/-- The choice that encodes `P` is not 0 iff `P`. -/
theorem sel_ne (P : Prop) [Decidable P] :
    (((if P then cOne else cZero).val != 0#u8) = true) ↔ P := by
  split <;> simp_all [cOne_val, cZero_val]

/-- The choice that encodes `P` is 1 iff `P`. -/
theorem sel_one (P : Prop) [Decidable P] : ((if P then cOne else cZero).val = 1#u8) ↔ P := by
  split <;> simp_all [cOne_val, cZero_val]

/-- The negation of the choice `a` is 1 iff `a` is not 1. -/
theorem not_one (a : subtle.Choice) :
    ((if a.val = 1#u8 then cZero else cOne).val = 1#u8) ↔ ¬ a.val = 1#u8 := by
  split <;> simp_all [cOne_val, cZero_val]

/-- If `decRes` rejects, it is related to `none`. -/
theorem decRes_none (S I : _root_.field.Fe) (ws : Bool)
    (h : ws = false ∨ negP (decX S I * decY S I) ∨ decY S I = 0) :
    DecRel (decRes S I ws) none := by
  unfold decRes
  rcases h with h1 | h1 | h1
  · rw [h1]; rfl
  · cases ws
    · rfl
    · rw [if_pos rfl, if_pos h1]; rfl
  · cases ws
    · rfl
    · rw [if_pos rfl]
      split
      all_goals rfl

/-- If `decRes` accepts, it is related to the real point with the same coordinates. -/
theorem decRes_some (S I : _root_.field.Fe) (ws : Bool) (pt : ristretto.RistrettoPoint)
    (h1 : ws = true) (h2 : ¬ negP (decX S I * decY S I)) (h3 : ¬ decY S I = 0)
    (hpt : toZPt pt = (decX S I, decY S I, 1, decX S I * decY S I)) (hb : BndPt 52 pt) :
    DecRel (decRes S I ws) (some pt) := by
  unfold decRes
  rw [if_pos h1, if_neg h2, if_neg h3]
  exact ⟨hpt.symm, hb⟩

/-- The main path of `decompress`: after `step_1` accepted a canonical, nonnegative `s`. -/
theorem decompress_main (b : Array U8 32#usize) (s : FE) (hlt : U8x32_as_Nat b < p)
    (hS : ((U8x32_as_Nat b : Nat) : _root_.field.Fe) = toZ s) (hn : ¬ (toZ s).val % 2 = 1)
    (bs : Bnd 51 s) :
    (do
      let (ok1, t_is_negative, y_is_zero, res) ← ristretto.decompress.step_2 s
      let c2 ← subtle.Choice.Insts.CoreOpsBitNotChoice.not ok1
      let c3 ← subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor c2 t_is_negative
      let c4 ← subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor c3 y_is_zero
      if (c4.val != 0#u8) = true then ok none else ok (some res)) ⦃ r =>
      ∃ q, ristretto_ref.decode b = ok q ∧ DecRel q r ⦄ := by
  step with step_2_z as ⟨ok1, tn, yz, pt, ws, I, hws, hwsiff, hX, hY, hZ, hT, htn, hyz,
    bX, bY, bZ, bT⟩
  rw [not_eq, bind_ok, bitor_eq, bind_ok, bitor_eq, bind_ok]
  have href := ref_decode_main b hlt (toZ s) hS hn ws I hws
  have hX' : toZ pt.X = decX (toZ s) I := hX
  have hY' : toZ pt.Y = decY (toZ s) I := hY
  have hT' : toZ pt.T = decX (toZ s) I * decY (toZ s) I := by rw [hT, hX', hY']
  have hrej : ((if (if (if ok1.val = 1#u8 then cZero else cOne).val = 1#u8 ∨ tn.val = 1#u8
        then cOne else cZero).val = 1#u8 ∨ yz.val = 1#u8 then cOne else cZero).val != 0#u8)
        = true ↔
      (ws = false ∨ negP (decX (toZ s) I * decY (toZ s) I) ∨
        decY (toZ s) I = 0) := by
    rw [sel_ne, sel_one, not_one, ← hwsiff, htn, hyz, hT', hY']
    cases ws <;> simp [negP]
  by_cases hr : ((if (if (if ok1.val = 1#u8 then cZero else cOne).val = 1#u8 ∨ tn.val = 1#u8
        then cOne else cZero).val = 1#u8 ∨ yz.val = 1#u8 then cOne else cZero).val != 0#u8)
        = true
  · rw [if_pos hr, spec_ok]
    exact ⟨_, href, decRes_none _ _ _ (hrej.mp hr)⟩
  · rw [if_neg hr, spec_ok]
    have hn' := fun h => hr (hrej.mpr h)
    have hws1 : ws = true := by
      cases ws
      · exact absurd (Or.inl rfl) hn'
      · rfl
    exact ⟨_, href, decRes_some _ _ _ pt hws1 (fun h => hn' (Or.inr (Or.inl h)))
      (fun h => hn' (Or.inr (Or.inr h))) (by simp only [toZPt, hX', hY', hZ, hT'])
      ⟨bX, bY, bZ, bT⟩⟩

/-- Decoding refines the reference. For every 32-byte `b`, `decompress b` returns without
panic, overflow or divergence, the reference `decode b` returns `ok q`, and `DecRel q r`
holds. So either both reject, with the reference error 20, or both accept with the same
four coordinates in `ZMod p`, and the limbs of the real point are below `2 ^ 52`. -/
theorem decompress_refines (b : Array U8 32#usize) :
    ristretto.CompressedRistretto.decompress b ⦃ r =>
      ∃ q, ristretto_ref.decode b = ok q ∧ DecRel q r ⦄ := by
  unfold ristretto.CompressedRistretto.decompress
  step with step_1_z as ⟨cc, cn, s, hcc, hcn, hsz, bs⟩
  rw [not_eq, bind_ok, bitor_eq, bind_ok]
  simp only [bool_from, bind_ok]
  by_cases hlt : U8x32_as_Nat b < p
  · -- canonical encoding
    have hc1 : cc.val = 1#u8 := hcc.mpr hlt
    have h255 : U8x32_as_Nat b < 2 ^ 255 := lt_of_lt_of_le hlt (by rw [p_val]; omega)
    have hS : ((U8x32_as_Nat b : Nat) : _root_.field.Fe) = toZ s := by
      rw [hsz, Nat.mod_eq_of_lt h255]; rfl
    rw [if_pos hc1, cZero_val]
    by_cases hn : (toZ s).val % 2 = 1
    · have hcn1 : cn.val = 1#u8 := hcn.mpr hn
      rw [if_pos (Or.inr hcn1), cOne_val, if_pos (by decide), spec_ok]
      exact ⟨_, ref_decode_neg b hlt (toZ s) hS hn, rfl⟩
    · have hcn1 : ¬ cn.val = 1#u8 := fun h => hn (hcn.mp h)
      have hor : ¬ ((0#u8 : U8) = 1#u8 ∨ cn.val = 1#u8) := fun h =>
        h.elim (fun h' => absurd h' (by decide)) hcn1
      rw [if_neg hor, cZero_val, if_neg (by decide)]
      exact decompress_main b s hlt hS hn bs
  · -- non-canonical encoding: both reject
    have hc1 : ¬ cc.val = 1#u8 := fun h => hlt (hcc.mp h)
    rw [if_neg hc1, cOne_val, if_pos (Or.inl rfl), cOne_val, if_pos (by decide), spec_ok]
    exact ⟨_, ref_decode_noncanon b hlt, rfl⟩

end RistrettoSim
