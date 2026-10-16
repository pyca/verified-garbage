module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.X448.Arm
meta import VerifiedGarbage.Impl.X448.Arm
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# X448 on ARMv7: the field functions as literals

The callers' literals refer to these (`materialize_code`), so the kernel
builds each function's code once.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.mulFn
materialize_code Impl.X448.Arm.addFn
materialize_code Impl.X448.Arm.subFn
materialize_code Impl.X448.Arm.mulA24Fn

end VG
