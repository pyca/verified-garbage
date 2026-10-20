module

public import VerifiedGarbage.Impl.CmacTripleDes.Arm
import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.Arm
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! # TDEA-CMAC's ARMv7 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.Arm.init
materialize_code Impl.CmacTripleDes.Arm.update
materialize_code Impl.CmacTripleDes.Arm.finalize

end VG
