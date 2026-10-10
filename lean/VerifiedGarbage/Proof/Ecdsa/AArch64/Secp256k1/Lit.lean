import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.Secp256k1Literals

/-!
# ECDSA over secp256k1 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG

materialize_code Impl.Ecdsa.AArch64.signSecp256k1

end VG
