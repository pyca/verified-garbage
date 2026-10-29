module

public import VerifiedGarbage.Impl.Secp256k1.X86_64.PointOps
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.PointOps
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! secp256k1's point functions' code as literals (`materialize_code`), which
their checks read rather than build each field operation again. -/

@[expose] public section

namespace VG.Impl.Secp256k1.X86_64.PointOps

materialize_code addCachedLit := addCachedFn
materialize_code addAffineLit := addAffineFn

end VG.Impl.Secp256k1.X86_64.PointOps
