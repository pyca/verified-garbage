module

public import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SM4 on Arm: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

materialize_flat_code expandKeyCode := Impl.Sm4.Arm.expandKey
materialize_flat_code ecbAnyCode := Impl.Sm4.Arm.ecbAny

end VG.Proof.Sm4.Arm
