module

public import VerifiedGarbage.Impl.P384.X86_64.PointOps
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.P384.X86_64.PointOps
import VerifiedGarbage.Impl.Weierstrass.X86_64.JointDouble
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.JointDouble
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! P-384's point functions' code as literals (`materialize_code`), which their
checks read rather than build each field operation again. -/

@[expose] public section

namespace VG.Impl.P384.X86_64.PointOps

materialize_code addCachedLit := addCachedFn false
materialize_code addCachedAdxLit := addCachedFn true
materialize_code addAffineLit := addAffineFn false
materialize_code addAffineAdxLit := addAffineFn true

end VG.Impl.P384.X86_64.PointOps
