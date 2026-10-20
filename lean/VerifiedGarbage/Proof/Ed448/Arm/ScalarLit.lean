module

public import VerifiedGarbage.Impl.Ed448.Arm.Scalar
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed448.Arm.Scalar
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Ed448 scalar arithmetic on ARMv7: the code as literals

The kernel checks each literal once; the taint checks reuse it.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.Arm.scalarReduce
materialize_code Impl.Ed448.Arm.scalarMulAdd

end VG
