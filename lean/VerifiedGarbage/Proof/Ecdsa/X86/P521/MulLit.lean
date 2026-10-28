module

public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
public import VerifiedGarbage.Impl.Ecdsa.P521.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# `vg_p521_mul` on x86 (32-bit): the code as a literal

`vg_p521_mul` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
which its constant time, `spSafe` and its stack evaluate.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.X86.mulP521

end VG
