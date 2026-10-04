import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed448.AArch64.Scalar

/-!
# Ed448 scalar arithmetic on AArch64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.AArch64.scalarReduce
materialize_code Impl.Ed448.AArch64.scalarMulAdd

end VG
