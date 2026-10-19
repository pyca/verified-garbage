module

public import VerifiedGarbage.Impl.EcKey.P521.AArch64
meta import VerifiedGarbage.Impl.EcKey.P521.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P521.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# P-521 public keys on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.AArch64.publicKeyP521

end VG
