module

public import VerifiedGarbage.Impl.P224.X86_64.PointOps
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.P224.X86_64.PointOps
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! P-224's point functions' code as literals (`materialize_code`), which
their checks read rather than build each field operation again. -/

@[expose] public section

namespace VG.Impl.P224.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.PointOps

/-- `vg_p224_jac_add_cached` with its call of `vg_p224_jac_add_tail` inlined
(`Code.inlineAll`): the code the table's proofs run. -/
def addCachedFlat : Prog isa := wrap (addCachedBody publicJoint.K publicJoint.selected dblJMul)

materialize_code addCachedLit := addCachedFlat

end VG.Impl.P224.X86_64.PointOps
