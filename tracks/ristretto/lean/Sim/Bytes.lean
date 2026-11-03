import RistrettoRef.Funs
import DalekSim.Bytes

/-! # Bytes and natural numbers

`U8x32_as_Nat` reads 32 bytes in little-endian order. The reference field model reads and
writes bytes with its own formulas (`fe_from_bytes`, `fe_to_bytes`). This file shows that the
two readings agree. The digit lemmas and the top-bit mask are in `DalekSim.Bytes`. -/

open Aeneas Aeneas.Std Result
open DalekSim

namespace RistrettoSim

/-- If `b` reads as `a.val`, then `fe_to_bytes a` returns `b`. -/
theorem fe_to_bytes_eq (a : _root_.field.Fe) (b : Array U8 32#usize)
    (h : U8x32_as_Nat b = (show ZMod _root_.field.p from a).val) :
    _root_.field.fe_to_bytes a = ok b := by
  unfold _root_.field.fe_to_bytes
  simp only [ok.injEq]
  apply Aeneas.Std.Array.ext
  rw [Array.from_val]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    apply UScalar.eq_of_val_eq
    rw [UScalar.ofNatCore_val_eq, ← h, U8x32_digit b i (by simpa using h1),
      getElem!_pos b.val i h2]

/-- `fe_from_bytes` reads the bytes as `U8x32_as_Nat`, reduced mod p. -/
theorem fe_from_bytes_eq (b : Array U8 32#usize) :
    _root_.field.fe_from_bytes b =
      ok ((U8x32_as_Nat b : ℕ) : _root_.field.Fe) := by
  unfold _root_.field.fe_from_bytes
  rw [foldr_horner (fun i => (b.val[i]!).val) 0 32, U8x32_as_Nat_eq, mul_zero, add_zero]

end RistrettoSim
