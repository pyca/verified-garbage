module

public import VerifiedGarbage.Proof.X448.Arm.FnLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# X448 on ARMv7: the code as a literal

Materializing the code once avoids rebuilding the unrolled arithmetic in each
kernel-evaluated check.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.x448

end VG
