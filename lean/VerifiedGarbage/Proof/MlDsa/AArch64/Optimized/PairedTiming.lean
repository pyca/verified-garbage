import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Coefficients and norm bounds remain secret. The z kernel only reveals
its buffers and the immutable inverse table address. -/
theorem z_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]))
    (selected .z) :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_PAIR"])
    (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The r0 schedule additionally reveals the public parameter gamma. -/
theorem r0_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5]))
    (selected .r0) :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_PAIR"])
    (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5]) (fun _ _ _ _ h => h) (by taint_decide)

/-- Hint values, counts and norm results do not affect the pair trace. -/
theorem h_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]))
    (selected .h) :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_INV_PAIR"])
    (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
