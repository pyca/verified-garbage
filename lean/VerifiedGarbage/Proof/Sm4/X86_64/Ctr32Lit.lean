module

public import VerifiedGarbage.Proof.Sm4.X86_64.Lit
public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr32
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Impl.Sm4.X86_64.Ctr32
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SM4's counter mode with `inc₃₂` on x86-64: the code as a literal

As `ModesLit.lean`, for `vg_sm4_ctr32`, whose code the checks of the whole
function (`taint_decide`, `lit_decide`: the ABI, the stack scratch and
`spSafe`) evaluate several times each.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

materialize_flat_code ctr32Code := Impl.Sm4.X86_64.ctr32

end VG.Proof.Sm4.X86_64
