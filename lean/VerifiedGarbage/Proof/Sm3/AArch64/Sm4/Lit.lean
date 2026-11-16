module

public import VerifiedGarbage.Impl.Sm3.AArch64.Sm4
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm3.AArch64.Sm4
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM3 with the AArch64 SM3 instructions: the code as a literal
-/

@[expose] public section

namespace VG.Impl.Sm3.AArch64.Sm4

materialize_code compress

end VG.Impl.Sm3.AArch64.Sm4
