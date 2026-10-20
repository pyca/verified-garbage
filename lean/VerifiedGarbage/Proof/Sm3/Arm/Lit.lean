module

public import VerifiedGarbage.Impl.Sm3.Arm.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm3.Arm.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SM3 on ARMv7: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.Arm.compress
materialize_code Impl.Sm3.Arm.Stream.update
materialize_code Impl.Sm3.Arm.Stream.finalize

end VG
