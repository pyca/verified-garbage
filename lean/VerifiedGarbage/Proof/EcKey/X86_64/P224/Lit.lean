module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
public import VerifiedGarbage.Impl.EcKey.P224.X86_64
meta import VerifiedGarbage.Impl.EcKey.P224.X86_64

/-!
# P-224 public keys on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.X86_64.publicKeyP224

end VG
