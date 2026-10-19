module

public import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-!
# X448 on ARMv7: the code as a literal

Materializing the code once avoids rebuilding the unrolled arithmetic in each
kernel-evaluated check.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.x448

end VG
