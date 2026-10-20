module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ECDSA verification over P-224 on x86-64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (`spSafe`, the ABI's checks):
the literal of the code (`materialize_code`, `Proof/Framework/Lit.lean`) is
checked once here instead.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.X86_64.jointVerifyP224

end VG
