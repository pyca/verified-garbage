module

public import VerifiedGarbage.Impl.Sha1.Arm.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha1.Arm.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SHA-1 on ARMv7: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha1.Arm.compress
materialize_code Impl.Sha1.Arm.Stream.update
materialize_code Impl.Sha1.Arm.Stream.finalize

end VG
