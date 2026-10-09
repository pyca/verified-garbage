import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal

theorem outer_checked : normalize outerSchedule = some standardOuter := by decide +kernel

theorem inner_checked : normalize innerSchedule = some standardInner := by decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
