module

public import VerifiedGarbage.Impl.Gcm.Arm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! # GHASH on ARMv7: the code as a literal, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Gcm.Arm
materialize_code ghash
end VG.Impl.Gcm.Arm
