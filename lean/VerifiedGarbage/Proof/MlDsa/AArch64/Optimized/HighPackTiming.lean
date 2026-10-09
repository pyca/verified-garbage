import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

/-- Coefficients stay secret; only the two buffer addresses are public. -/
theorem pack4_ct :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1]))
      (Impl.MlDsa.AArch64.Optimized.HighPack.code 261888) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem pack6_ct :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1]))
      (Impl.MlDsa.AArch64.Optimized.HighPack.code 95232) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
