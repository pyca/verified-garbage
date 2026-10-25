module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Scheduled
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

theorem scheduled_good : ∀ op ∈ scheduledOps, Good op := by decide +kernel

/-- Structural expression equality checks data dependencies, including the
original values preserved by both temporary slots. -/
theorem scheduled_symbolic : ∀ i < 25,
    (symRun scheduledOps symInitial).regs (laneReg i) =
    (symRun coreOps symInitial).regs (laneReg i) := by decide +kernel

theorem scheduled_matches (f : File) (i : Nat) (hi : i < 25) :
    (run scheduledOps f).regs (laneReg i) = (run coreOps f).regs (laneReg i) := by
  rw [run_regs, run_regs, scheduled_symbolic i hi]

end VG.Proof.Sha3.AArch64.Scalar
