import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal

theorem outer_checked :
    Schedule.check key mask ((List.range 8).map outerSlice) = some standardOuter := by
  decide +kernel

theorem inner_checked :
    Schedule.check key mask ((List.range 8).map innerSlice) = some standardInner := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
