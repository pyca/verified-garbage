import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.EcKey.P256.Arm

/-!
# P-256 public keys on 32-bit ARM: the code as a literal

As for the signature (`Proof/Ecdsa/Arm/Lit.lean`): the literal of the code is
checked once here, rather than rebuilt in every check that evaluates it.
-/

namespace VG

materialize_code Impl.EcKey.Arm.publicKeyP256

end VG
