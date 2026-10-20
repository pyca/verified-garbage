module

public import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ChaCha20 on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.Arm.block
materialize_code Impl.ChaCha20.Arm.Xor.xor

end VG
