module

public import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SEED on Arm: the code as literals

The code of the key expansion and of ECB in both directions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again in
each of them.
Not flattened (`materialize_flat_code`): its unfolding measured slower here.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

materialize_code expandKeyCode := Impl.Seed.Arm.expandKey
materialize_code ecbEncrypt := Impl.Seed.Arm.ecb .encrypt
materialize_code ecbDecrypt := Impl.Seed.Arm.ecb .decrypt

end VG.Proof.Seed.Arm
