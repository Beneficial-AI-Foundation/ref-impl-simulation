import X25519Ref.Funs

/-! Runs the Lean reference (`x25519_ref`, with the `ZMod p` field model) on the RFC 7748
vectors that `ref-plain` tests in Rust, and on the edge inputs of
`ref-plain/tests/edge.rs`. The iterated test of section 5.2 runs 1 and 1,000 iterations, not
1,000,000. This is a test with `#guard`, not a proof. Run with
`lake env lean Sim/RefVectors.lean` after `lake build`. The command fails if any check fails. -/

open Aeneas Aeneas.Std Result

namespace X25519RefVectors

def hexByte (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def byteAt (s : String) (i : Nat) : Nat :=
  let cs := s.toList
  (16 * hexByte (cs.getD (2 * i) '0') + hexByte (cs.getD (2 * i + 1) '0')) % 256

def bytes (s : String) : Array Std.U8 32#usize :=
  Array.from (List.ofFn (fun (i : Fin 32) =>
    UScalar.ofNatCore (ty := .U8) (byteAt s i.val) (by simp [byteAt]; omega))) (by simp)

def toNats (v : Array Std.U8 32#usize) : List Nat :=
  List.ofFn (fun (i : Fin 32) => (v.val[i.val]!).val)

def same (r : Result (Array Std.U8 32#usize)) (expected : String) : Bool :=
  match r.match with
  | .ok v => toNats v == List.ofFn (fun (i : Fin 32) => byteAt expected i.val)
  | _ => false

-- RFC 7748 section 5.2, first vector.
#guard same
  (x25519_ref.x25519_scalarmult
    (bytes "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
    (bytes "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"))
  "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"

-- RFC 7748 section 6.1, Alice's public key.
#guard same
  (x25519_ref.x25519_secret_to_public
    (bytes "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"))
  "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"

-- RFC 7748 section 5.2, second vector.
#guard same
  (x25519_ref.x25519_scalarmult
    (bytes "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d")
    (bytes "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"))
  "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"

/-- RFC 7748 section 5.2, the iterated test: from `k = u = 9`, set `u` to the old `k` and `k`
to the result, `n` times. -/
def iterate : Nat → Array Std.U8 32#usize → Array Std.U8 32#usize → Result (Array Std.U8 32#usize)
  | 0, k, _ => ok k
  | n + 1, k, u => do
    let r ← x25519_ref.x25519_scalarmult k u
    iterate n r k

def nine : Array Std.U8 32#usize :=
  bytes "0900000000000000000000000000000000000000000000000000000000000000"

#guard same (iterate 1 nine nine)
  "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"
#guard same (iterate 1000 nine nine)
  "684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51"

-- RFC 7748 section 6.1: Bob's public key, and the shared secret `K` from both sides.
def alice : String := "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
def alicePub : String := "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
def bob : String := "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"
def bobPub : String := "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
def sharedK : String := "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"

#guard same (x25519_ref.x25519_secret_to_public (bytes bob)) bobPub
#guard same (x25519_ref.x25519_scalarmult (bytes alice) (bytes bobPub)) sharedK
#guard same (x25519_ref.x25519_scalarmult (bytes bob) (bytes alicePub)) sharedK

-- Our addition `x25519_is_all_zero` (RFC 7748 section 6.1): false on `K`, true on 0.
def isZero (s : String) : Option Bool :=
  match (x25519_ref.x25519_is_all_zero (bytes s)).match with
  | .ok b => some b
  | _ => none

#guard isZero sharedK == some false
#guard isZero "0000000000000000000000000000000000000000000000000000000000000000" == some true
#guard isZero "0000000000000000000000000000000000000000000000000000000000000080" == some false

/-! ## Edge inputs, as in `ref-plain/tests/edge.rs` -/

/-- The scalar of RFC 7748 section 5.2, vector 1. -/
def K : String := "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"

def x (u : String) : Result (Array Std.U8 32#usize) := x25519_ref.x25519_scalarmult (bytes K) (bytes u)

def zero : String := "0000000000000000000000000000000000000000000000000000000000000000"

-- Low-order inputs give 0: 0, 1, p - 1, p, p + 1 and a point of order 8.
#guard same (x zero) zero
#guard same (x "0100000000000000000000000000000000000000000000000000000000000000") zero
#guard same (x "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") zero
#guard same (x "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") zero
#guard same (x "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") zero
#guard same (x "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800") zero

-- Fixed outputs, computed with the Rust port and checked against OpenSSL's X25519.
-- 2^255 - 1 = p + 18 gives the output of 18. Bit 255 set gives the output of the RFC u.
#guard same (x "0900000000000000000000000000000000000000000000000000000000000000")
  "1c9fd88f45606d932a80c71824ae151d15d73e77de38e8e000852e614fae7019"
#guard same (x "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f")
  "1c9fd88f45606d932a80c71824ae151d15d73e77de38e8e000852e614fae7019"
#guard same (x "1200000000000000000000000000000000000000000000000000000000000000")
  "76b00406ce7e87774c0038dd8d89b188047977f8828ca1dcb8f98bb5d5d0cf48"
#guard same (x "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f")
  "76b00406ce7e87774c0038dd8d89b188047977f8828ca1dcb8f98bb5d5d0cf48"
#guard same (x "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1ccc")
  "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"

-- Bits that clamping clears do not change the output.
#guard same
  (x25519_ref.x25519_scalarmult
    (bytes "a246e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449a04")
    (bytes "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"))
  "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"

end X25519RefVectors
