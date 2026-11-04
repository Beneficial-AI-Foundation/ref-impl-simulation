import Curve25519Dalek.Funs
import DalekSim.Basic
import DalekSim.Edwards
import DalekSim.BasepointTableData

/-! # The basepoint table

`ED25519_BASEPOINT_TABLE` is a 32 x 8 array of affine Niels points `(y + x, y - x, 2 d x y)`.
`basepoint_table` shows that entry `j` of row `i` is the point `[(j + 1) 256^i] B`, where `B`
is the basepoint of edwards25519 and the group law is the one of `DalekSim.Edwards`. Every
limb of the table is below `2^52`.

The proof has two parts.

1. `check` is a test on the natural numbers of the extracted limbs. It decodes each entry to an
   affine point mod `p`, and it tests that `xy2d` is `2 d x y`, that entry `j + 1` of a row is
   entry `j` plus entry 0, and that entry 0 of row `i + 1` is 8 doublings of entry 0 of row
   `i`. Each addition is a polynomial equation, with the denominators multiplied out. The
   doublings go through the witness points of `DalekSim.BasepointTableData`. The kernel runs
   `check` with `decide +kernel` in about 3 s.
2. `addRel_sound` turns one equation into the addition of `DalekSim.Edwards`, because the
   denominators are not 0 on the curve. An induction over the rows and the entries then gives
   the multiples of `B`.

The edit of `extract.sh` with `inline-table.py` makes the table one literal. Without it, the
kernel does not reduce the 768 binds of the Aeneas output. -/

open Aeneas Aeneas.Std Result curve25519_dalek
open backend.serial.curve_models backend.serial.u64

namespace DalekSim.BasepointTable

open Edwards

instance : Inhabited AffineNielsPoint := ⟨⟨default, default, default⟩⟩

/-! ## The test on natural numbers -/

/-- The value of five 51-bit limbs, by Horner's rule. `feNat_eq` shows that this is
`Field51_as_Nat`. -/
def feNat (fe : field.FieldElement51) : Nat :=
  fe.val.foldr (fun l acc => l.val + 2 ^ 51 * acc) 0

/-- Every limb is below `2^52`. -/
def limbsLt (fe : field.FieldElement51) : Bool := fe.val.all (fun l => l.val < 2 ^ 52)

/-- The inverse of 2 mod `p`. -/
def inv2 : Nat := (p + 1) / 2

/-- The affine point `(x, y)` mod `p` that an entry `(y + x, y - x, 2 d x y)` encodes. -/
def affine (e : AffineNielsPoint) : Nat × Nat :=
  let a := feNat e.y_plus_x % p
  let b := feNat e.y_minus_x % p
  ((a + p - b) * inv2 % p, (a + b) * inv2 % p)

/-- The limbs of the entry are below `2^52`, and `xy2d` is `2 d x y` mod `p`. -/
def nielsOK (e : AffineNielsPoint) : Bool :=
  limbsLt e.y_plus_x && limbsLt e.y_minus_x && limbsLt e.xy2d &&
  feNat e.xy2d % p == 2 * d * (affine e).1 * (affine e).2 % p

/-- `R = P + Q` by the unified addition, with the denominators multiplied out. -/
def addRel (P Q R : Nat × Nat) : Bool :=
  let t := d * P.1 * Q.1 * P.2 * Q.2 % p
  R.1 * (1 + t) % p == (P.1 * Q.2 + P.2 * Q.1) % p &&
  R.2 * (1 + p - t) % p == (P.2 * Q.2 + P.1 * Q.1) % p

/-- Every entry of the row passes `nielsOK`, and entry `j + 1` is entry `j` plus entry 0. -/
def rowOK (row : window.LookupTable AffineNielsPoint) : Bool :=
  row.val.all nielsOK &&
  (List.range 7).all fun j => addRel (affine row.val[j]!) (affine row.val[0]!) (affine row.val[j + 1]!)

/-- Entry 0 of row `i + 1` is 8 doublings of entry 0 of row `i`, through the points `w`. -/
def transOK (T : edwards.EdwardsBasepointTable) (i : Nat) (w : List (Nat × Nat)) : Bool :=
  w[0]! == affine T.val[i]!.val[0]! && w[8]! == affine T.val[i + 1]!.val[0]! &&
  (List.range 8).all fun k => addRel w[k]! w[k]! w[k + 1]!

/-- The x-coordinate of the basepoint. -/
def Bx : Nat := 15112221349535400772501151409588531511454012693041857206046113283949847762202

/-- The y-coordinate of the basepoint, `4 / 5` mod `p`. -/
def By : Nat := 46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- The test of the whole table. -/
def check (T : edwards.EdwardsBasepointTable) : Bool :=
  affine T.val[0]!.val[0]! == (Bx, By) && T.val.all rowOK &&
  (List.range 31).all fun i => transOK T i witnesses[i]!

/-- The table is a literal that passes `check`. -/
theorem check_table : ∃ T, constants.ED25519_BASEPOINT_TABLE = ok T ∧ check T = true := by
  refine ⟨?T, ?h1, ?h2⟩
  case h1 =>
    unfold constants.ED25519_BASEPOINT_TABLE constants.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN
    rfl
  case h2 => decide +kernel

/-! ## From natural numbers to `ZMod p` -/

/-- A pair of natural numbers as a point over `ZMod p`. -/
def toZ (P : Nat × Nat) : ZMod p × ZMod p := ((P.1 : ZMod p), (P.2 : ZMod p))

/-- `feNat` is `Field51_as_Nat`. -/
theorem feNat_eq (fe : field.FieldElement51) : feNat fe = Field51_as_Nat fe := by
  have hl : fe.val.length = 5 := fe.property
  simp only [feNat, Field51_as_Nat, Finset.sum_range_succ, Finset.sum_range_zero,
    Array.getElem!_Nat_eq]
  generalize fe.val = l at hl ⊢
  match l, hl with
  | [a0, a1, a2, a3, a4], _ => simp; ring

/-- `limbsLt` gives the limb bound `Bnd 52`. -/
theorem bnd_of_limbsLt {fe : field.FieldElement51} (h : limbsLt fe = true) : Bnd 52 fe := by
  intro i hi
  have hl : i < fe.val.length := by simpa using hi
  rw [Array.getElem!_Nat_eq, getElem!_pos fe.val i hl]
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hl))

/-- `2 * inv2 = 1` in `ZMod p`. -/
theorem two_mul_inv2 : (2 : ZMod p) * (inv2 : ZMod p) = 1 := by
  have h : 2 * inv2 = p + 1 := by unfold inv2 p; decide +kernel
  have := congrArg (fun n : Nat => (n : ZMod p)) h
  simpa using this

/-- An equation of natural numbers mod `p` is an equation in `ZMod p`. -/
theorem cast_of_mod {a b : Nat} (h : a % p = b % p) : (a : ZMod p) = (b : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff' a b p).mpr h

/-- The entry encodes the point `affine e`: `y + x`, `y - x` and `2 d x y` mod `p`. -/
theorem affine_spec {e : AffineNielsPoint} (h : nielsOK e = true) :
    (Field51_as_Nat e.y_plus_x : ZMod p) = (toZ (affine e)).2 + (toZ (affine e)).1 ∧
    (Field51_as_Nat e.y_minus_x : ZMod p) = (toZ (affine e)).2 - (toZ (affine e)).1 ∧
    (Field51_as_Nat e.xy2d : ZMod p) = 2 * dEd * (toZ (affine e)).1 * (toZ (affine e)).2 := by
  simp only [nielsOK, Bool.and_eq_true, beq_iff_eq] at h
  have hx := cast_of_mod h.2
  push_cast [ZMod.natCast_mod] at hx
  have h2 := two_mul_inv2
  have hb : feNat e.y_minus_x % p ≤ feNat e.y_plus_x % p + p :=
    le_add_left (Nat.mod_lt _ (by unfold p; decide)).le
  simp only [toZ, ← feNat_eq]
  refine ⟨?_, ?_, by rw [hx, dEd]⟩
  · simp only [affine]
    push_cast [Nat.cast_sub hb, ZMod.natCast_mod, ZMod.natCast_self]
    linear_combination (-(feNat e.y_plus_x : ZMod p)) * h2
  · simp only [affine]
    push_cast [Nat.cast_sub hb, ZMod.natCast_mod, ZMod.natCast_self]
    linear_combination (-(feNat e.y_minus_x : ZMod p)) * h2

/-- One equation of `addRel` is the addition of `DalekSim.Edwards`, for points on the curve. -/
theorem addRel_sound {P Q R : Nat × Nat} (hP : OnCurve dEd (toZ P)) (hQ : OnCurve dEd (toZ Q))
    (h : addRel P Q R = true) : toZ R = add dEd (toZ P) (toZ Q) := by
  simp only [addRel, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hx, hy⟩ := h
  have ht : d * P.1 * Q.1 * P.2 * Q.2 % p ≤ 1 + p :=
    (Nat.mod_lt _ (by unfold p; decide)).le.trans (Nat.le_add_left _ _)
  have cx := cast_of_mod hx
  have cy := cast_of_mod hy
  push_cast [Nat.cast_sub ht, ZMod.natCast_mod, ZMod.natCast_self] at cx cy
  have n1 := one_add_ne_zero hP hQ
  have n2 := one_sub_ne_zero hP hQ
  simp only [toZ, dEd] at n1 n2 ⊢
  simp only [add, Prod.mk.injEq]
  constructor
  · rw [eq_div_iff n1]; linear_combination cx
  · rw [eq_div_iff n2]; linear_combination cy

/-! ## The basepoint -/

/-- The basepoint is on the curve. -/
theorem onCurve_B : OnCurve dEd (toZ (Bx, By)) := by
  have h : (By * By) % p = (1 + d * Bx * Bx * By * By + Bx * Bx) % p := by
    unfold Bx By d p; decide +kernel
  have := cast_of_mod h
  push_cast at this
  simp only [OnCurve, toZ, dEd]
  linear_combination this

/-- The basepoint `B` of edwards25519. -/
def B : Point dEd := ⟨toZ (Bx, By), onCurve_B⟩

/-- `B` has the y-coordinate `4 / 5`. -/
theorem B_y : 5 * B.1.2 = 4 := by
  have h : (5 * By) % p = 4 % p := by unfold By p; decide +kernel
  simpa [B, toZ] using cast_of_mod h

/-- The x-coordinate of `B`, as a natural number below `p`, is even. -/
theorem Bx_even : Bx < p ∧ Bx % 2 = 0 := by unfold Bx p; decide +kernel

/-! ## The rows and the entries -/

/-- Entry 0 of row `i` is `[256^i] B`. -/
theorem row_spec {T : edwards.EdwardsBasepointTable} (h : check T = true) :
    ∀ i < 32, toZ (affine T.val[i]!.val[0]!) = ((256 ^ i) • B).1 := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h0, -⟩, htr⟩ := h
  intro i hi
  induction i with
  | zero => rw [pow_zero, one_nsmul, h0]; rfl
  | succ i ih =>
    have ht := htr i (by omega)
    simp only [transOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ht
    obtain ⟨⟨hw0, hw8⟩, hdbl⟩ := ht
    -- Witness `k` is `[2^k 256^i] B`.
    have hk : ∀ k ≤ 8, toZ (witnesses[i]!)[k]! = ((2 ^ k * 256 ^ i) • B).1 := by
      intro k hk
      induction k with
      | zero => rw [hw0, ih (by omega), pow_zero, one_mul]
      | succ k ihk =>
        have hc : OnCurve dEd (toZ (witnesses[i]!)[k]!) := by
          rw [ihk (by omega)]; exact ((2 ^ k * 256 ^ i) • B).2
        rw [addRel_sound hc hc (hdbl k (by omega)), ihk (by omega), ← Point.val_two_mul_nsmul]
        congr 2; ring
    rw [← hw8, hk 8 le_rfl]
    congr 2; ring

/-- Entry `j` of row `i` is `[(j + 1) 256^i] B`. -/
theorem entry_spec {T : edwards.EdwardsBasepointTable} (h : check T = true) :
    ∀ i < 32, ∀ j < 8, toZ (affine T.val[i]!.val[j]!) = (((j + 1) * 256 ^ i) • B).1 := by
  have hrow := row_spec h
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  intro i hi j hj
  have hi' : i < T.val.length := by simpa using hi
  have hr := h.1.2 _ (List.getElem_mem hi')
  rw [← getElem!_pos T.val i hi'] at hr
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hr
  induction j with
  | zero => simpa using hrow i hi
  | succ j ihj =>
    have hP : OnCurve dEd (toZ (affine T.val[i]!.val[j]!)) := by
      rw [ihj (by omega)]; exact (((j + 1) * 256 ^ i) • B).2
    have hQ : OnCurve dEd (toZ (affine T.val[i]!.val[0]!)) := by
      rw [hrow i hi]; exact ((256 ^ i) • B).2
    rw [addRel_sound hP hQ (hr.2 j (by omega)), ihj (by omega), hrow i hi, ← Point.val_add,
      ← add_nsmul]
    congr 2; ring

/-- Every entry of the table passes `nielsOK`. -/
theorem niels_spec {T : edwards.EdwardsBasepointTable} (h : check T = true) :
    ∀ i < 32, ∀ j < 8, nielsOK T.val[i]!.val[j]! = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  intro i hi j hj
  have hi' : i < T.val.length := by simpa using hi
  have hr := h.1.2 _ (List.getElem_mem hi')
  rw [← getElem!_pos T.val i hi'] at hr
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true] at hr
  have hj' : j < T.val[i]!.val.length := by simpa using hj
  rw [getElem!_pos _ j hj']
  exact hr.1 _ (List.getElem_mem hj')

/-! ## The theorem -/

/-- The basepoint table of curve25519-dalek: entry `j` of row `i` encodes the point
`P = [(j + 1) 256^i] B` as `(y + x, y - x, 2 d x y)` with `P = (x, y)`, and every limb is below
`2^52`. -/
theorem basepoint_table : ∃ T, constants.ED25519_BASEPOINT_TABLE = ok T ∧
    ∀ i < 32, ∀ j < 8,
      Bnd 52 ((T[i]!)[j]!).y_plus_x ∧ Bnd 52 ((T[i]!)[j]!).y_minus_x ∧ Bnd 52 ((T[i]!)[j]!).xy2d ∧
      (Field51_as_Nat ((T[i]!)[j]!).y_plus_x : ZMod p) =
        (((j + 1) * 256 ^ i) • B).1.2 + (((j + 1) * 256 ^ i) • B).1.1 ∧
      (Field51_as_Nat ((T[i]!)[j]!).y_minus_x : ZMod p) =
        (((j + 1) * 256 ^ i) • B).1.2 - (((j + 1) * 256 ^ i) • B).1.1 ∧
      (Field51_as_Nat ((T[i]!)[j]!).xy2d : ZMod p) =
        2 * dEd * (((j + 1) * 256 ^ i) • B).1.1 * (((j + 1) * 256 ^ i) • B).1.2 := by
  obtain ⟨T, hT, h⟩ := check_table
  refine ⟨T, hT, fun i hi j hj => ?_⟩
  have hn := niels_spec h i hi j hj
  have he := entry_spec h i hi j hj
  simp only [Array.getElem!_Nat_eq]
  rw [← he]
  have hb : limbsLt T.val[i]!.val[j]!.y_plus_x = true ∧ limbsLt T.val[i]!.val[j]!.y_minus_x =
      true ∧ limbsLt T.val[i]!.val[j]!.xy2d = true := by
    simp only [nielsOK, Bool.and_eq_true] at hn
    exact ⟨hn.1.1.1, hn.1.1.2, hn.1.2⟩
  exact ⟨bnd_of_limbsLt hb.1, bnd_of_limbsLt hb.2.1, bnd_of_limbsLt hb.2.2, affine_spec hn⟩

/--
info: 'DalekSim.BasepointTable.basepoint_table' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms basepoint_table

end DalekSim.BasepointTable
