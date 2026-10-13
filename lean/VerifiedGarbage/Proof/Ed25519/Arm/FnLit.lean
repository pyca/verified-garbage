module

public import VerifiedGarbage.Impl.Ed25519.Arm.Power
meta import VerifiedGarbage.Impl.Ed25519.Arm.Power
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! The functions of point arithmetic and the inversion chain, and their
bodies, as literals (`materialize_code`), which their own constant-time
checks and the literals of the code that calls them read rather than build
each field multiplication again. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

materialize_code pointAdd
materialize_code pointDouble
materialize_code chain250
materialize_code Point16.addFn
materialize_code Point16.doubleFn
materialize_code pow250Fn

end VG.Impl.Ed25519.Arm
