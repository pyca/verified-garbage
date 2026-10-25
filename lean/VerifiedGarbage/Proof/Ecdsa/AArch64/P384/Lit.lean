module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.P384.Ops
import VerifiedGarbage.Impl.Weave
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
meta import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-!
# ECDSA over P-384 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.AArch64.signP384

end VG
