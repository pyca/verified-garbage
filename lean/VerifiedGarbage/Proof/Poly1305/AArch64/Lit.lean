module

public import VerifiedGarbage.Impl.Poly1305.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Poly1305.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Poly1305 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.AArch64.init
materialize_code Impl.Poly1305.AArch64.blocks

end VG
