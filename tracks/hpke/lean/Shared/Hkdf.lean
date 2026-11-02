/-
Shared model of the HKDF primitives (RFC 5869 over RFC 2104 HMAC).
Both the reference (hacspec cryptolib stubs) and the real code (any
`HpkeCrypto` instance) are tied to this one model, so the simulation
theorem does not relate two unrelated sets of axioms.

The only opaque parts are the hash: `hmacBlock` (HMAC on a normalised key) and
`longKey` (the hashed form of a key longer than the block). HKDF-Extract and
HKDF-Expand are defined from them as in RFC 5869.
-/
module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

namespace Shared

inductive Hash | sha256 | sha384 | sha512
deriving DecidableEq, Inhabited

/-- Block length B of the hash, in bytes (RFC 2104). -/
def blockLen : Hash → Nat
  | .sha256 => 64
  | .sha384 => 128
  | .sha512 => 128

instance : Inhabited (alloc.vec.Vec U8) := ⟨alloc.vec.Vec.new U8⟩

/-- HMAC key for keys longer than B: H(K) padded. Opaque. -/
opaque longKey : Hash → List U8 → List U8

/-- RFC 2104 step 1: a key of at most B bytes is padded on the right with zero bytes. -/
def normKey (h : Hash) (k : List U8) : List U8 :=
  if k.length ≤ blockLen h then k ++ List.replicate (blockLen h - k.length) 0#u8
  else longKey h k

/-- Output length L of the hash, in bytes. -/
def hashLen : Hash → Nat
  | .sha256 => 32
  | .sha384 => 48
  | .sha512 => 64

instance (h : Hash) : Inhabited {l : List U8 // l.length = hashLen h} :=
  ⟨⟨List.replicate (hashLen h) 0#u8, by simp⟩⟩

/-- HMAC on an already normalised (B-byte) key: an L-byte tag.
This is the one opaque HMAC/SHA-2. -/
opaque hmacBlock : (h : Hash) → List U8 → List U8 → {l : List U8 // l.length = hashLen h}

theorem hashLen_le (h : Hash) : hashLen h ≤ Usize.max := by
  have : (64 : Nat) ≤ Usize.max := by scalar_tac
  cases h <;> simp [hashLen] <;> omega

/-- HKDF-Extract(salt, ikm) = HMAC(salt, ikm). -/
def extract (h : Hash) (salt ikm : List U8) : alloc.vec.Vec U8 :=
  alloc.vec.Vec.from (hmacBlock h (normKey h salt) ikm).val
    (by rw [(hmacBlock h (normKey h salt) ikm).property]; exact hashLen_le h)

theorem extract_length (h : Hash) (salt ikm : List U8) : (extract h salt ikm).val.length = hashLen h := by
  simp [extract, (hmacBlock h (normKey h salt) ikm).property]

/-- The blocks `T(i) ‖ T(i+1) ‖ …` of RFC 5869 §2.3, `n` blocks from index `i`, where
`prev` is `T(i-1)` and `T(i) = HMAC(key, T(i-1) ‖ info ‖ i)`. -/
def expandBlocks (h : Hash) (key info : List U8) : Nat → Nat → List U8 → List U8
  | 0, _, _ => []
  | n + 1, i, prev =>
    let t := (hmacBlock h key (prev ++ info ++ [@UScalar.mk UScalarTy.U8 (BitVec.ofNat 8 i)])).val
    t ++ expandBlocks h key info n (i + 1) t

theorem expand_bound (h : Hash) (L : Nat) (hL : L ≤ 255 * hashLen h) (l : List U8) :
    (l.take L).length ≤ Usize.max := by
  have : (255 * 64 : Nat) ≤ Usize.max := by scalar_tac
  have : hashLen h ≤ 64 := by cases h <;> simp [hashLen]
  have := List.length_take_le L l
  omega

/-- HKDF-Expand(PRK, info, L) (RFC 5869 §2.3). It fails (`none`) if `L > 255 * HashLen`.
Otherwise it returns the first `L` bytes of `T(1) ‖ … ‖ T(N)` with `N = ⌈L / HashLen⌉`. -/
def expand (h : Hash) (prk info : List U8) (L : Nat) : Option (alloc.vec.Vec U8) :=
  if hL : L ≤ 255 * hashLen h then
    some (alloc.vec.Vec.from
      ((expandBlocks h (normKey h prk) info ((L + hashLen h - 1) / hashLen h) 1 []).take L)
      (expand_bound h L hL _))
  else none

/-- HKDF-Expand succeeds for every output length allowed by RFC 5869. -/
theorem expand_ne_none (h : Hash) (prk info : List U8) (L : Nat) (hL : L ≤ 255 * hashLen h) :
    expand h prk info L ≠ none := by
  simp [expand, hL]

/-- The salt `[0x00]` and the empty salt give the same HMAC key, hence the same PRK. -/
theorem extract_salt_zero (h : Hash) (ikm : List U8) :
    extract h [0#u8] ikm = extract h [] ikm := by
  cases h <;> simp [extract, normKey, blockLen, List.replicate_succ]

end Shared
