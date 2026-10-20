module

import VerifiedGarbage.Proof.Idea.KeyLit32
public import VerifiedGarbage.Impl.Idea.Arm
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Impl.Idea.Arm
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-! # Literal IDEA programs for kernel-evaluated checks (ARMv7) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.Arm.expandKey
materialize_code Impl.Idea.Arm.invertKey
materialize_code Impl.Idea.Arm.ecb

end VG
