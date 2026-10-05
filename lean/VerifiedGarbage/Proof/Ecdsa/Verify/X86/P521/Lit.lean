import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86

/-!
# ECDSA verification over P-521 on x86 (32-bit): the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.X86.verifyP521

end VG
