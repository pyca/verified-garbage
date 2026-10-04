import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.Arm

/-!
# ECDSA verification over P-256 on 32-bit ARM: the code as a literal

As for the signature (`Proof/Ecdsa/Arm/Lit.lean`): the literal of the code is
checked once here, rather than rebuilt in every check that evaluates it.
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.Arm.verifyP256

end VG
