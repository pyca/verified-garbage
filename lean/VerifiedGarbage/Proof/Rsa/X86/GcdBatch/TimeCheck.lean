module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
meta import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
meta import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint

/-! # The fixed GCD kernels leak only public workspace addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86

theorem body66_check :
    (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 66 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 66)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 66 15))
        (VG.Impl.Rsa.X86.GcdBatch.body 66))).isSome=true := by
  taint_decide

theorem body98_check :
    (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 98 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 98)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 98 15))
        (VG.Impl.Rsa.X86.GcdBatch.body 98))).isSome=true := by
  taint_decide

theorem body130_check :
    (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 130 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 130)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 130 15))
        (VG.Impl.Rsa.X86.GcdBatch.body 130))).isSome=true := by
  taint_decide

end VG.Proof.Rsa.X86.GcdBatch
