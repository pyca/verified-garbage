module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialLoop
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialLoop
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! The table loop reveals only its public word count and addresses. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

/-- Candidate bounds, table pointer, and table count are public. The packed
prime word and accumulated divisibility flag need not be public. -/
def trialLoopTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [36], bases := [(.esp, 0, 0)],
    slots := [(0, 0, 16)] }

private theorem certificate : ∃ hc,
    (VG.Taint.check taint trialLoopTaint Impl.Dsa.X86.Generation.trialLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem trial_loop_ct : RelCT isa (VG.X86.Taint.Agree trialLoopTaint)
    Impl.Dsa.X86.Generation.trialLoop (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := certificate
  exact RelCT.taint (A := taint) trialLoopTaint (fun _ _ h => h) checked

end VG.Proof.Dsa.X86.Generation
