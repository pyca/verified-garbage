module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
meta import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
meta import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint

/-! # The fixed GCD kernels leak only public workspace addresses

The checker receives an explicit certificate, so the kernel validates it
without repeating the invariant search in `hintOf`.

The unrolled blocks use 128-instruction certificate intervals. More frequent
checked intermediate taints reduce kernel evaluation compared with the
default 1024/256 intervals, without changing the analysis or its obligations. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86

theorem body66_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 66 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 66)
      hint).isSome=true := by
  exact ⟨_, by run_tac VG.taintDecideAt (Lean.mkNatLit 128) "taint_decide" none⟩

theorem body98_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 98 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 98)
      hint).isSome=true := by
  exact ⟨_, by run_tac VG.taintDecideAt (Lean.mkNatLit 128) "taint_decide" none⟩

theorem body130_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 130 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 130)
      hint).isSome=true := by
  exact ⟨_, by run_tac VG.taintDecideAt (Lean.mkNatLit 128) "taint_decide" none⟩

end VG.Proof.Rsa.X86.GcdBatch
