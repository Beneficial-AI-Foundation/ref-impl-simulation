import X25519Ref.Funs

/-! Runs the Lean reference (`x25519_ref`, with the `ZMod p` field model) on the two
RFC 7748 vectors that `ref-plain` tests in Rust, and on the edge inputs of
`ref-plain/tests/edge.rs`. This is a test with `#guard`, not a proof. Run with
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
