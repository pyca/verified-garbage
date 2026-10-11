import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.P384.X86_64.PointOps

/-! P-384's point functions' code as literals (`materialize_code`), which their
checks read rather than build each field operation again. -/

namespace VG.Impl.P384.X86_64.PointOps

materialize_code addCachedLit := addCachedFn false
materialize_code addCachedAdxLit := addCachedFn true
materialize_code addAffineLit := addAffineFn false
materialize_code addAffineAdxLit := addAffineFn true

end VG.Impl.P384.X86_64.PointOps
