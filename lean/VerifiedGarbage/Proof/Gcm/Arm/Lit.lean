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

/-! # `vg_ghash` on ARM, as a literal

For the checks of every instruction and the constant-time analyses that
evaluate it. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.Arm.ghash

end VG
