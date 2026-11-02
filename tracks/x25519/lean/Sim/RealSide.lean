import Sim.Discharge
import Sim.RefSide
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Field.FieldElement51.Invert

/-! # dalek's Montgomery ladder in closed form

The ladder loop `mul_loop` swaps lazily: it keeps the two points in physical order and a bit
`prev`. Its logical state is `cswap prev (x0, x1)`. `mul_loop_spec` shows that the logical
state follows `lstep` on the key bits, under `toZ`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
open X25519Sim.LadderMath

namespace X25519Sim

/-- A projective point as a pair of reference field elements. -/
def toP (P : montgomery.ProjectivePoint) : Pt _root_.field.Fe := (toZ P.U, toZ P.W)

/-- Both coordinates have limbs below `2 ^ 52`. -/
def BndP (P : montgomery.ProjectivePoint) : Prop := Bnd 52 P.U ∧ Bnd 52 P.W

theorem fe_eq_make (a : FE) (h0 : 0 < a.val.length) (h1 : 1 < a.val.length)
    (h2 : 2 < a.val.length) (h3 : 3 < a.val.length) (h4 : 4 < a.val.length)
    (hl : [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4]].length = (5#usize).val) :
    Array.make 5#usize [a.val[0], a.val[1], a.val[2], a.val[3], a.val[4]] hl = a := by
  apply Aeneas.Std.Array.ext
  rw [Array.make_val]
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> rfl

theorem fe_select_eq (a b : FE) (c : subtle.Choice) :
    backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_select
      a b c = ok (if c.val = 1#u8 then b else a) := by
  unfold backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_select
  by_cases hc : c.val = 1#u8 <;>
    simp [hc, U64.Insts.SubtleConditionallySelectable.conditional_select, Array.index_usize,
      fe_eq_make]


theorem pp_swap_eq (x0 x1 : montgomery.ProjectivePoint) (c : subtle.Choice) :
    subtle.ConditionallySelectable.conditional_swap.default
      montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable x0 x1 c =
      ok (if c.val = 1#u8 then (x1, x0) else (x0, x1)) := by
  unfold subtle.ConditionallySelectable.conditional_swap.default
  simp only [montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select,
    fe_select_eq, bind_ok]
  by_cases hc : c.val = 1#u8 <;> simp [hc]

theorem choice_from_spec (x : U8) (hx : x.val ≤ 1) :
    subtle.Choice.Insts.CoreConvertFromU8.from x ⦃ c => c.val = x ⦄ := by
  unfold subtle.Choice.Insts.CoreConvertFromU8.from
  by_cases h0 : x = 0#u8
  · rw [dif_pos h0, spec_ok]
  · have h1 : x = 1#u8 := by
      apply UScalar.eq_of_val_eq
      have : x.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simp [h]))
      simp; omega
    rw [dif_neg h0, dif_pos h1, spec_ok]

theorem choice_from_bool (b : Bool) :
    subtle.Choice.Insts.CoreConvertFromU8.from (UScalar.cast_fromBool .U8 b) ⦃ c =>
      (c.val = 1#u8 ↔ b = true) ⦄ := by
  unfold subtle.Choice.Insts.CoreConvertFromU8.from
  cases b <;> simp only [UScalar.cast_fromBool, Bool.false_eq_true, if_false, if_true]
  · rw [dif_pos (by rfl), spec_ok]; decide
  · rw [dif_neg (by decide), dif_pos (by rfl), spec_ok]; simp; rfl

/-- `i &&& 7` is `i % 8` on a small nonnegative `Isize`, on 32-bit and 64-bit platforms. -/
theorem isize_and7 (i : Isize) (h0 : 0 ≤ i.val) (_h1 : i.val ≤ 254) : (i &&& 7#isize).val = i.val % 8 := by
  have hw : 32 ≤ System.Platform.numBits := by cases System.Platform.numBits_eq <;> omega
  have hn : IScalarTy.Isize.numBits = System.Platform.numBits := rfl
  simp only [IScalar.val] at h0 ⊢
  have hand : (i &&& 7#isize).bv = i.bv &&& (7#isize).bv := rfl
  rw [hand]
  have hpow : (2:ℕ) ^ 32 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by norm_num) hw
  have h7 : (7#isize).bv.toNat = 7 := by
    have : (7#isize).val = 7 := by simp
    simp only [IScalar.val, BitVec.toInt_eq_toNat_cond] at this
    split_ifs at this <;> omega
  have hpow' : (2:ℕ) ^ 32 ≤ 2 ^ IScalarTy.Isize.numBits := hpow
  simp only [BitVec.toInt_eq_toNat_cond] at h0 ⊢
  rw [BitVec.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod _ 3]
  have hlt' : ((i.bv.toNat : ℕ) : ℤ) < (2 : ℤ) ^ IScalarTy.Isize.numBits := by
    exact_mod_cast i.bv.isLt
  generalize i.bv.toNat = x at *
  split_ifs at h0 ⊢ <;> push_cast at * <;> omega

theorem hcast_small (x : Isize) (h0 : 0 ≤ x.val) (h1 : x.val < 256) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  have hw : 32 ≤ System.Platform.numBits := by cases System.Platform.numBits_eq <;> omega
  have hpow : (256 : ℤ) ≤ 2 ^ UScalarTy.Usize.numBits := by
    have : (2 : ℤ) ^ 8 ≤ 2 ^ UScalarTy.Usize.numBits :=
      pow_le_pow_right₀ (by norm_num) (by simp)
    simpa using this
  rw [IScalar.hcast_val_eq, Int.emod_eq_of_lt h0 (by omega)]

/-- The bit read at the start of each loop iteration. -/
def read_bit (scalar_bytes : Array U8 32#usize) (i : Isize) : Result Bool := do
  let i1 ← i >>> 3#i32
  let byte_idx ← lift (IScalar.hcast .Usize i1)
  let i2 ← lift (i &&& 7#isize)
  let bit_idx ← lift (IScalar.hcast .Usize i2)
  let i3 ← Array.index_usize scalar_bytes byte_idx
  let i4 ← i3 >>> bit_idx
  let i5 ← lift (i4 &&& 1#u8)
  ok (i5 = 1#u8)

theorem read_bit_spec (k : Array U8 32#usize) (i : Isize) (h0 : 0 ≤ i.val) (h1 : i.val ≤ 254) :
    read_bit k i ⦃ b => b = kbit k i.val.toNat ⦄ := by
  unfold read_bit
  have hw : 32 ≤ System.Platform.numBits := by cases System.Platform.numBits_eq <;> omega
  step*
  all_goals
    have hi1 : i1.val = i.val / 8 := by rw [i1_post, Int.shiftRight_eq_div_pow]; norm_num
    have hb : byte_idx.val = i.val.toNat / 8 := by
      rw [byte_idx_post, hcast_small i1 (by omega) (by omega), hi1]; omega
    have hi2 : i2.val = i.val % 8 := by rw [i2_post, isize_and7 i h0 h1]
    have hbit : bit_idx.val = i.val.toNat % 8 := by
      rw [bit_idx_post, hcast_small i2 (by omega) (by omega), hi2]; omega
  · simp only [hb, Array.length]; simp; omega
  · rw [hbit]; omega
  · have h8 : i.val.toNat / 8 < k.val.length := by simp; omega
    have hi5 : i5.val = (k.val[i.val.toNat / 8]!.val >>> (i.val.toNat % 8)) % 2 := by
      simp [i5_post, i4_post, i3_post, hb, hbit, getElem!_pos k.val (i.val.toNat / 8) h8,
        Nat.and_one_is_mod]
    have e : (i5 = 1#u8) ↔ i5.val = 1 :=
      ⟨fun h => by simp [h], fun h => UScalar.eq_of_val_eq (by simp [h])⟩
    simp only [kbit, ← hi5, e]
    cases h : (i5.val == 1) <;> simp_all


abbrev mulLoop := Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_loop

set_option maxRecDepth 4096 in
theorem mul_loop_unfold (u : FE) (x0 x1 : montgomery.ProjectivePoint) (k : Array U8 32#usize)
    (prev : Bool) (i : Isize) :
    mulLoop u x0 x1 k prev i =
      if i >= 0#isize then do
        let bit ← read_bit k i
        let choice ← lift (UScalar.cast_fromBool .U8 (prev != bit))
        massert ((choice = 0#u8) || (choice = 1#u8))
        let c ← core.convert.IntoFrom.into subtle.Choice.Insts.CoreConvertFromU8 choice
        let (x01, x11) ← subtle.ConditionallySelectable.conditional_swap.default
          montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable x0 x1 c
        let (x02, x12) ← montgomery.differential_add_and_double x01 x11 u
        let i6 ← i - 1#isize
        mulLoop u x02 x12 k bit i6
      else ok (x0, x1, prev) := by
  rw [mulLoop, Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint.mul_loop]
  simp only [read_bit, Std.bind_assoc, Std.bind_ok]

/-- Both points of a pair as reference field elements. -/
def toP2 (S : montgomery.ProjectivePoint × montgomery.ProjectivePoint) :
    Pt _root_.field.Fe × Pt _root_.field.Fe := (toP S.1, toP S.2)

theorem toP2_cswap (b : Bool) (S : montgomery.ProjectivePoint × montgomery.ProjectivePoint) :
    toP2 (cswap b S) = cswap b (toP2 S) := by
  cases b <;> rfl

/-- The step theorem with the reference step written as `pad`. -/
theorem dad_spec (P Q : montgomery.ProjectivePoint) (u : FE) (hP : BndP P) (hQ : BndP Q)
    (hu : Bnd 54 u) :
    montgomery.differential_add_and_double P Q u ⦃ r =>
      toP2 r = pad (toZ u) (toP2 (P, Q)) ∧ BndP r.1 ∧ BndP r.2 ⦄ := by
  apply spec_mono (differential_add_and_double_refines_proved P Q u
    (bnd_mono hP.1 (by norm_num)) (bnd_mono hP.2 (by norm_num))
    (bnd_mono hQ.1 (by norm_num)) (bnd_mono hQ.2 (by norm_num)) hu 1)
  rintro r ⟨s, hs, h1, h2, h3, h4, b1, b2, b3, b4⟩
  rw [point_add_and_double_pad] at hs
  simp only [ok.injEq] at hs
  refine ⟨?_, ⟨b1, b2⟩, ⟨b3, b4⟩⟩
  rw [← hs] at h1 h2 h3 h4
  exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)

theorem mul_loop_spec (u : FE) (hu : Bnd 54 u) (k : Array U8 32#usize) :
    ∀ (n : Nat) (i : Isize) (x0 x1 : montgomery.ProjectivePoint) (prev : Bool),
      i.val + 1 = n → n ≤ 255 → BndP x0 → BndP x1 →
      mulLoop u x0 x1 k prev i ⦃ r =>
        toP2 (cswap r.2.2 (r.1, r.2.1)) = ladder (toZ u) (bitsFrom k n) (toP2 (cswap prev (x0, x1))) ∧
        BndP r.1 ∧ BndP r.2.1 ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i x0 x1 prev hi _ h0 h1
    rw [mul_loop_unfold]
    have : ¬ (i >= 0#isize) := by scalar_tac
    simp only [this, if_false, spec_ok]
    exact ⟨rfl, h0, h1⟩
  | succ n ih =>
    intro i x0 x1 prev hi hn h0 h1
    rw [mul_loop_unfold]
    have hge : i >= 0#isize := by scalar_tac
    simp only [hge, if_true]
    step with read_bit_spec k i (by omega) (by omega) as ⟨bit, hbit⟩
    step as ⟨choice, hchoice⟩
    have hle : choice.val ≤ 1 := by rw [hchoice]; cases (prev != bit) <;> simp
    step as ⟨⟩
    step with choice_from_spec choice hle as ⟨c, hc⟩
    have key : (c.val = 1#u8) ↔ (prev ^^ bit) = true := by
      rw [hc]
      constructor
      · intro h; have := congrArg UScalar.val h; rw [hchoice] at this
        cases hpb : (prev != bit) <;> simp_all
      · intro h; apply UScalar.eq_of_val_eq; rw [hchoice]
        have : (prev != bit) = true := by simpa using h
        simp [this]
    have hsw : (if c.val = 1#u8 then (x1, x0) else (x0, x1)) = cswap (prev ^^ bit) (x0, x1) := by
      by_cases h : c.val = 1#u8
      · rw [if_pos h, key.mp h]; rfl
      · have : (prev ^^ bit) = false := by simpa [key] using h
        rw [if_neg h, this]; rfl
    rw [pp_swap_eq]
    simp only [bind_ok, hsw]
    have hB : BndP (cswap (prev ^^ bit) (x0, x1)).1 ∧ BndP (cswap (prev ^^ bit) (x0, x1)).2 := by
      cases (prev ^^ bit) <;> simp [cswap, h0, h1]
    generalize hS : cswap (prev ^^ bit) (x0, x1) = S at hB
    obtain ⟨y0, y1⟩ := S
    step with dad_spec y0 y1 u hB.1 hB.2 hu as ⟨x02, x12, hr, br1, br2⟩
    step as ⟨i6, hi6⟩
    apply spec_mono (ih i6 x02 x12 bit (by omega) (by omega) br1 br2)
    rintro r ⟨hr', b1, b2⟩
    refine ⟨?_, b1, b2⟩
    rw [hr', bitsFrom_succ, ladder_cons]
    congr 1
    rw [toP2_cswap, hr, ← hS, toP2_cswap, lstep, toP2_cswap, cswap_cswap, hbit,
      show i.val.toNat = n by omega]

end X25519Sim
