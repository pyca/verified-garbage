import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase

/-!
# Ed448 base-point multiplication on ARMv7: the code as a literal

The kernel checks the literal once; the taint check reuses it.
-/

namespace VG

materialize_code Impl.Ed448.Arm.scalarBase

end VG
