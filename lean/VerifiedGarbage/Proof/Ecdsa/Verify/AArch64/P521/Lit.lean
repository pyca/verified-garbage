import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.PowLit
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64

/-!
# ECDSA verification over P-521 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead, reading the
literal of the power modulo `n` (`PowLit.lean`).
-/

namespace VG

materialize_code Impl.Ecdsa.Verify.AArch64.verifyP521

end VG
