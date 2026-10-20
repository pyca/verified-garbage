module

public import VerifiedGarbage.Proof.X448.X86.FnLit
public import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.X448.X86.FnLit
meta import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Ed448 verification's equation on x86 (32-bit): the code as a literal

The field arithmetic is fully unrolled: the literal of the code
(`materialize_code`, `Proof/Framework/Lit.lean`) spares the kernel building
the instructions again in every check that evaluates the code (constant time,
`spSafe`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86.verifyEquation

end VG
