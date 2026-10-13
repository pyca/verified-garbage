module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
public import VerifiedGarbage.Impl.X448.Arm
meta import VerifiedGarbage.Impl.X448.Arm
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X448 on ARMv7: the code as a literal

Materializing the code once avoids rebuilding the unrolled arithmetic in each
kernel-evaluated check.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.x448

end VG
