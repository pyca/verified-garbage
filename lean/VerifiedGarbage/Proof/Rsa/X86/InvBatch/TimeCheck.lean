module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
meta import VerifiedGarbage.Impl.Rsa.X86.InvBatch
meta import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint

/-! # Constant-time checks for complete active-width inversion kernels -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86

theorem body64_check :
    (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 64 15))
      (VG.Impl.Rsa.X86.InvBatch.body 64 32)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 64 15))
        (VG.Impl.Rsa.X86.InvBatch.body 64 32))).isSome=true := by
  taint_decide

theorem body96_check :
    (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 96 15))
      (VG.Impl.Rsa.X86.InvBatch.body 96 48)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 96 15))
        (VG.Impl.Rsa.X86.InvBatch.body 96 48))).isSome=true := by
  taint_decide

theorem body128_check :
    (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 128 15))
      (VG.Impl.Rsa.X86.InvBatch.body 128 64)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 128 15))
        (VG.Impl.Rsa.X86.InvBatch.body 128 64))).isSome=true := by
  taint_decide

end VG.Proof.Rsa.X86.InvBatch
