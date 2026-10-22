module

public import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr32
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Impl.Sm4.AArch64.Ctr32
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM4's counter mode with `inc₃₂` on AArch64: the code as a literal

As `Lit.lean`, for `vg_sm4_ctr32`, whose code the checks of the whole
function (`taint_decide_sum`, `lit_decide`) evaluate.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

materialize_flat_code ctr32Code := Impl.Sm4.AArch64.ctr32

end VG.Proof.Sm4.AArch64
