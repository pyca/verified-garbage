module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal

theorem outer_checked :
    Schedule.check key mask ((List.range 8).map outerSlice) = some standardOuter := by
  decide +kernel

theorem inner_checked :
    Schedule.check key mask ((List.range 8).map innerSlice) = some standardInner := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
