module

import VerifiedGarbage.Proof.Mcdt.X86_64.Op
meta import VerifiedGarbage.Proof.Mcdt.X86_64.Op

/-!
# A call of `vg_mcdt_enter` in the x86-64 taint analyses

Code that calls `vg_mcdt_enter`, tests its result and branches on it, as
`Rust.mcdtOpen` asks of code whose affected instructions run only where it
returned 1, is constant time by `taintMx` with the call as an operation
(`enterOpMx`): its result is public. Without the operation, the analysis
follows the call into `vg_mcdt_enter`, whose frame it does not handle.
A summary of such code (`taint_summary_ops`) is an operation too, which
applies to its calls from more public. The residue analysis (`rtaintMx`)
takes the call as an operation too (`enterOpR`).
-/

namespace VG.Test.X86_64McdtOp

open VG VG.X86_64 VG.Proof.Mcdt.X86_64

/-- `n` (in `rdx`) kept in `r9` across the call, then a branch on its
result: `rdx` restored on both paths, and on the path where it returned 1,
a load through `rdi`. -/
def guarded : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rdx)])
    (.seq (.call "vg_mcdt_enter" Impl.Mcdt.X86_64.enterCall)
      (.seq (.block [.alu32 .test .rax (.reg .rax)])
        (.ite .e (.block [.mov .rdx (.reg .r9)])
          (.block [.mov .rdx (.reg .r9), .mov .rax (.mem { base := .rdi }), .alu .cmp .rdx (.reg .rsi)]))))

/-- The taint on entry: the arguments and `rsp` public. -/
def τ₀ : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]

theorem guarded_sem : VG.Taint.Sem taintMx τ₀ guarded := by taint_decide_ops [enterOpMx_ok]

/-- Constant time, from states that agree on the arguments, `rsp` and MXCSR. -/
theorem guarded_ct : ConstantTime isa (fun _ => True)
    (fun s₁ s₂ => (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s₁.gpr r = s₂.gpr r) ∧ s₁.mxcsr = s₂.mxcsr) guarded :=
  VG.Taint.constantTime_of_sem (A := taintMx) τ₀ (fun _ _ _ _ h => ⟨Taint.agree_ofRegs h.1, h.2⟩) guarded_sem

-- The analysis alone does not follow the call (its frame).
#guard (VG.Taint.hint taintMx 256 τ₀ guarded).isNone

-- A call of `guarded` as a function, summarized.
taint_summary_ops guardedSum : taintMx τ₀ (.call "vg_f" guarded) using enterOpMx_ok

/-- Two calls of it, the second from more public (`rcx`). -/
def twice : Prog isa :=
  .seq (.call "vg_f" guarded) (.seq (.block [.mov .rcx (.imm 1)]) (.call "vg_f" guarded))

theorem twice_sem : VG.Taint.Sem taintMx τ₀ twice := by taint_decide_ops [guardedSum]

/-- The residue analysis of `guarded`, with 16 bytes of stack (the call's
return address and the frame of `vg_mcdt_enter`): it follows the call as an
operation, and finds the window the same in both runs at the end. -/
theorem guarded_res : VG.Taint.OpsCheck rtaintMx [enterOpR] (RScrub.init Spec.Mcdt.enterSig 16) guarded
    (RScrub.resOkB · 16 [] (Impl.Scrub.X86_64.chunks 16)) := by
  taint_decide_ops_check

-- The granules to wipe: none.
#guard keep_for_ops% Spec.Mcdt.enterSig 16 guarded [enterOpR] == []

end VG.Test.X86_64McdtOp
