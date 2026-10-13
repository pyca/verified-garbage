module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.P384.X86_64.PointOps
meta import VerifiedGarbage.Impl.P384.X86_64.PointOps
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! P-384's point functions' code as literals (`materialize_code`), which their
checks read rather than build each field operation again. -/

@[expose] public section

namespace VG.Impl.P384.X86_64.PointOps

materialize_code addCachedLit := addCachedFn false
materialize_code addCachedAdxLit := addCachedFn true
materialize_code addAffineLit := addAffineFn false
materialize_code addAffineAdxLit := addAffineFn true

end VG.Impl.P384.X86_64.PointOps
