import X25519Ref.Funs

/-! Runs the Lean reference (`x25519_ref`, with the `ZMod p` field model) on the two
RFC 7748 vectors that `ref-plain` tests in Rust. This is a test with `#eval`, not a proof.
Run with `lake env lean Sim/RefVectors.lean` after `lake build`. Each line prints `true`
when the Lean reference gives the RFC output. -/

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
#eval same
  (x25519_ref.x25519_scalarmult
    (bytes "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
    (bytes "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"))
  "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"

-- RFC 7748 section 6.1, Alice's public key.
#eval same
  (x25519_ref.x25519_secret_to_public
    (bytes "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"))
  "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"

end X25519RefVectors
