import Curve25519Dalek.Math.Basic

/-! # The Edwards parameter `d`

`d` of `Curve25519Dalek.Math.Basic` as an element of `ZMod p`, with the two facts that the
Edwards-to-Montgomery map needs. -/

namespace DalekSim

/-- The Edwards parameter `d = -121665 / 121666` of Curve25519. -/
def dEd : ZMod p := (d : ZMod p)

/-- `d` is not a square in `ZMod p`. -/
theorem dEd_not_square : ¬IsSquare dEd := by
  apply (legendreSym.eq_neg_one_iff' p).mp
  norm_num [dEd, d, p]

/-- `121666 d = -121665` in `ZMod p`. -/
theorem dEd_rel : 121666 * dEd = -121665 := by
  unfold dEd d p
  decide +kernel

end DalekSim
