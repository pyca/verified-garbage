module

public import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Poly1305.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Poly1305 on X86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.X86.init
materialize_code Impl.Poly1305.X86.blocks
materialize_code Impl.Poly1305.X86.update
materialize_code Impl.Poly1305.X86.finalize

end VG
