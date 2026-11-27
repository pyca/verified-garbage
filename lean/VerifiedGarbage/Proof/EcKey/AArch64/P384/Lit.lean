module

public import VerifiedGarbage.Impl.EcKey.P384.AArch64
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.EcKey.P384.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P384Literals
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# P-384 public keys on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead. The comb is the
signatures', whose literal (`Proof/Ecdsa/AArch64/P384/Lit.lean`) this one reads.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.AArch64.publicKeyP384

end VG
