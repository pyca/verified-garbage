import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed448.X86.Scalar

/-!
# Ed448 scalar arithmetic on x86 (32-bit): the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.X86.scalarReduce
materialize_code Impl.Ed448.X86.scalarMulAdd

end VG
