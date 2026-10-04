import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ed448.Arm.Scalar

/-!
# Ed448 scalar arithmetic on ARMv7: the code as literals

The kernel checks each literal once; the taint checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.Arm.scalarReduce
materialize_code Impl.Ed448.Arm.scalarMulAdd

end VG
