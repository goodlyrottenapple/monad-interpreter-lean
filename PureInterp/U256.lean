import PureInterp.Handlers.Add
import Std.Tactic.BVDecide

/-!
# 256-bit words as four 64-bit limbs

The interpreter stores an EVM word as four little-endian 64-bit limbs. This
file relates the limb-level results the handlers compute to `BitVec 256`
arithmetic.
-/

namespace PureInterp
open RiscvZkvm.Rv64 PureInterp.Handlers

/-- The word whose limbs are `l0` (least significant) to `l3`. -/
def ofLimbs (l0 l1 l2 l3 : Word) : BitVec 256 := l3 ++ l2 ++ l1 ++ l0

/-- The limbs the ADD handler writes are the limbs of the 256-bit sum. -/
theorem add_limbs_eq (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    ofLimbs (b0 + a0)
      (a1 + b1 + cb (b0 + a0) b0)
      (a2 + b2 + (cb (a1 + b1) a1 ||| cb (a1 + b1 + cb (b0 + a0) b0) (a1 + b1)))
      (a3 + b3 + (cb (a2 + b2) a2 |||
        cb (a2 + b2 + (cb (a1 + b1) a1 ||| cb (a1 + b1 + cb (b0 + a0) b0) (a1 + b1))) (a2 + b2)))
    = ofLimbs a0 a1 a2 a3 + ofLimbs b0 b1 b2 b3 := by
  simp only [ofLimbs, cb]
  bv_decide

end PureInterp
