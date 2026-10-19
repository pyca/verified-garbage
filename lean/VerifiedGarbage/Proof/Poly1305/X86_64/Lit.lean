module

public import VerifiedGarbage.Impl.Poly1305.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# Poly1305 on X86_64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.X86_64.init
materialize_code Impl.Poly1305.X86_64.blocks
materialize_code Impl.Poly1305.X86_64.updatePre
materialize_code Impl.Poly1305.X86_64.updatePost
materialize_code Impl.Poly1305.X86_64.finalize

end VG
