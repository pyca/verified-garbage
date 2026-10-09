import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Only buffer and immutable-table addresses are public; all coefficients remain secret. -/
theorem staticNtt_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_NTT_EXPANDED"] (Taint.ofRegs [.x0])) staticNtt :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_NTT_EXPANDED"]) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem outNtt_ct : ConstantTime isa (fun _ => True)
    (Taint.AgreeS ["VG_MLDSA_NTT_EXPANDED"] (Taint.ofRegs [.x0,.x1])) outNtt :=
  VG.Taint.constantTime (A := taintS ["VG_MLDSA_NTT_EXPANDED"]) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized
