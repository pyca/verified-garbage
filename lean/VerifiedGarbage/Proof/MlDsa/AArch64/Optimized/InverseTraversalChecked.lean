import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal

theorem local_checked : normalize localSchedule = some standardLocal := by decide +kernel

theorem strided_checked : normalize stridedSchedule = some standardStrided := by decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
