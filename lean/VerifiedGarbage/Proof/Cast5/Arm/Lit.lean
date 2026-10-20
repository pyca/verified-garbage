module

public import VerifiedGarbage.Impl.Cast5.Arm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`). -/

@[expose] public section

namespace VG.Impl.Cast5.Arm
materialize_code ecbEncrypt
materialize_code ecbDecrypt
materialize_code expandKey
end VG.Impl.Cast5.Arm
