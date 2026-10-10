import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
import VerifiedGarbage.Impl.Ecdh.P224.X86_64

/-!
# ECDH over P-224 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

namespace VG

materialize_code Impl.Ecdh.X86_64.exchangeP224

end VG
