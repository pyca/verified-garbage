module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
public import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86_64

/-!
# ECDSA over P-224 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.X86_64.signP224

end VG
