module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
public import VerifiedGarbage.Impl.Ecdsa.P384.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# ECDSA over P-384 on x86 (32-bit): the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.X86.signP384

end VG
