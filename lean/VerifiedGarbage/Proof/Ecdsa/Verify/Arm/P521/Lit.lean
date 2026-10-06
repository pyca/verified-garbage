import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.Arm

/-!
# ECDSA verification over P-521 on 32-bit ARM: the code as a literal

As for the signature (`Proof/Ecdsa/Arm/Lit.lean`): the literal of the code is
checked once here, rather than rebuilt in every check that evaluates it.
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.Arm.verifyP521

end VG
