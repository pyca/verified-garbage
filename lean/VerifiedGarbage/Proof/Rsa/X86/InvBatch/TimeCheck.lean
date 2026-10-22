module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
meta import VerifiedGarbage.Impl.Rsa.X86.InvBatch
meta import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint

/-! # Constant-time checks for complete active-width inversion kernels

The checker receives an explicit certificate, so the kernel validates it
without repeating the invariant search in `hintOf`. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86

theorem body64_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 64 15))
      (VG.Impl.Rsa.X86.InvBatch.body 64 32)
      hint).isSome=true := by
  exact ⟨_, by taint_decide⟩

theorem body96_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 96 15))
      (VG.Impl.Rsa.X86.InvBatch.body 96 48)
      hint).isSome=true := by
  exact ⟨_, by taint_decide⟩

theorem body128_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset 128 15))
      (VG.Impl.Rsa.X86.InvBatch.body 128 64)
      hint).isSome=true := by
  exact ⟨_, by taint_decide⟩

end VG.Proof.Rsa.X86.InvBatch
