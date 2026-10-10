import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.P224Literals

/-!
# ECDSA over P-224 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG

materialize_code Impl.Ecdsa.AArch64.signP224

end VG
