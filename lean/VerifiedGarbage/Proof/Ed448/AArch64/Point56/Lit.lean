module

public import VerifiedGarbage.Impl.Ed448.AArch64.Point56
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed448.AArch64.Point56
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literals of the AArch64 point functions' code (`vg_ed448_r56_point_double`,
`vg_ed448_r56_point_add`, `vg_gf448_r56_pow_p34`), which the checks of their
proofs evaluate: each is built once, here. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG.Impl.X448.AArch64 (slot)

-- The doubling's and the addition's operations, the bodies of their functions.
materialize_code dblBody := Impl.X448.AArch64.Fast.ops (Impl.Ed448.AArch64.dblOps (slot 3) (slot 4) (slot 5))
materialize_code addBody := Impl.X448.AArch64.Fast.ops
  (Impl.X448.AArch64.Base.addOps (slot 3) (slot 4) (slot 5) (slot 6) (slot 7) (slot 8))

end VG.Proof.Ed448.AArch64.Point56

namespace VG

materialize_code Impl.Ed448.AArch64.Point56.doubleFn
materialize_code Impl.Ed448.AArch64.Point56.addFn
materialize_code Impl.Ed448.AArch64.Point56.powFn

end VG
