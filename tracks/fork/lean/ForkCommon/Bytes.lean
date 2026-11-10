import Proofs.Helpers.AsNat

/-! # Byte lemmas shared by `ForkSim` and `ForkRistretto`

The two reference libraries `X25519Ref` and `RistrettoRef` both declare the root namespace
`field`, so no module imports both. These lemmas do not mention `field`, so both proof
libraries import them from here. -/

open Aeneas Aeneas.Std

namespace ForkCommon

/-- The reference reads bytes with `foldr` over the indices. This is `Nat.ofDigits 256`. -/
theorem foldr_range_eq_ofDigits (l : List ℕ) :
    (List.range l.length).foldr (fun i acc => acc * 256 + l[i]!) 0 = Nat.ofDigits 256 l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, ih, Nat.ofDigits_cons]
    ring

/-- Index `i` of the list of byte values is the value of byte `i`. -/
theorem map_val_getElem! (b : Array U8 32#usize) (i : ℕ) :
    (b.val.map (fun x => x.val))[i]! = (b.val[i]!).val := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  cases b.val[i]? <;> rfl

end ForkCommon
