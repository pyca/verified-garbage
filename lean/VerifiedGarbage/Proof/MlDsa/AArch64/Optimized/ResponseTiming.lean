import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Response

theorem addNorm_ct : ConstantTime isa (fun _ => True) (Taint.AgreeS [] (Taint.ofRegs [.x0,.x1])) addNorm :=
  VG.Taint.constantTime (A := taintS []) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem subLowNorm_ct : ConstantTime isa (fun _ => True) (Taint.AgreeS [] (Taint.ofRegs [.x0,.x1,.x2,.x3])) subLowNorm :=
  VG.Taint.constantTime (A := taintS []) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem hintNorm_ct : ConstantTime isa (fun _ => True) (Taint.AgreeS [] (Taint.ofRegs [.x0,.x1,.x2])) hintNorm :=
  VG.Taint.constantTime (A := taintS []) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem canonicalize_ct : ConstantTime isa (fun _ => True) (Taint.AgreeS [] (Taint.ofRegs [.x0])) canonicalize :=
  VG.Taint.constantTime (A := taintS []) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.Response
