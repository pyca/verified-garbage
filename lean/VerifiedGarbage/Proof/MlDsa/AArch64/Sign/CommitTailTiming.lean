import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64

/-- Both absorbed streams remain secret. Only the six buffer pointers
influence the helper's fixed memory trace. The nonce value is not public. -/
theorem code65_ct :
    ConstantTime isa (fun _=>True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6]))
      (Impl.MlDsa.AArch64.Sign.CommitTail.code 768 48) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])
    (fun _ _ _ _ h=>h) (by taint_decide)

/-- The longer commitment uses the same secret-input trace policy. -/
theorem code87_ct :
    ConstantTime isa (fun _=>True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6]))
      (Impl.MlDsa.AArch64.Sign.CommitTail.code 1024 64) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])
    (fun _ _ _ _ h=>h) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
