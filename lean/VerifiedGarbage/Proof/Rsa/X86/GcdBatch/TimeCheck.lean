module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint

/-! # The fixed GCD kernels leak only public workspace addresses

The checker receives an explicit certificate, so the kernel validates it
without repeating the invariant search in `hintOf`.

The unrolled blocks use 128-instruction certificate intervals. More frequent
checked intermediate taints reduce kernel evaluation compared with the
default 1024/256 intervals, without changing the analysis or its obligations.

The kernel reads the code of the 2048- and 3072-bit kernels from literals
(`materialize_flat_code`) rather than rebuilding it from the generators; the
4096-bit kernel's literal is too deep for the kernel to check. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86

materialize_flat_code body66 := VG.Impl.Rsa.X86.GcdBatch.body 66

theorem body66_check :
    ∃ hint, (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.GcdBatch.offset 66 15))
      (VG.Impl.Rsa.X86.GcdBatch.body 66)
      hint).isSome=true := by
  exact ⟨_, by run_tac VG.taintDecideAt (Lean.mkNatLit 128) "taint_decide" none⟩

materialize_flat_code body98 := VG.Impl.Rsa.X86.GcdBatch.body 98

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
