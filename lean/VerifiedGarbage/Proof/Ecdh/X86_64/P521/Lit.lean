module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P521Literals
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdh.P521.X86_64
meta import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ECDH over P-521 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, `spSafe`): the
literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdh.X86_64.exchangeP521

end VG
