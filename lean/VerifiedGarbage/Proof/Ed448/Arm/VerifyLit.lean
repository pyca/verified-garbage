import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation

/-!
# Ed448 verification's equation on ARMv7: the code as a literal

The kernel checks the literal once; the taint check reuses it.
-/

namespace VG

materialize_code Impl.Ed448.Arm.verifyEquation

end VG
