module

public import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# Ed448 base-point multiplication on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.scalarBase

end VG

namespace VG.Proof.Ed448.X86_64

theorem scalarBase_inlineOk : Impl.Ed448.X86_64.scalarBase.InlineOk = true := by lit_decide

end VG.Proof.Ed448.X86_64
