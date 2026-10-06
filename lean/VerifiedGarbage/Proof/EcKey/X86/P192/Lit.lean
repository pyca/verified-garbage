import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.EcKey.P192.X86

/-!
# P-192 public keys on x86 (32-bit): the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG

materialize_code Impl.EcKey.X86.publicKeyP192

end VG
