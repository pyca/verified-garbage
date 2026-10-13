module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Ed448.Arm.Scalar
meta import VerifiedGarbage.Impl.Ed448.Arm.Scalar
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Ed448 scalar arithmetic on ARMv7: the code as literals

The kernel checks each literal once; the taint checks reuse it.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.Arm.scalarReduce
materialize_code Impl.Ed448.Arm.scalarMulAdd

end VG
