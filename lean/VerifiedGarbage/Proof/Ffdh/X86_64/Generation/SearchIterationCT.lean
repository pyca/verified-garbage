module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchBranch
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassifyCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Constant-time native search iterations, including internal candidate calls -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private theorem branch_ct (v : RoundImpl) :
    RelCT isa (Two SearchRemainingGuard)
      (.ite .e exhausted (.seq (candidateRun (candidateCode v)) classify)) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact search_exhausted_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
  · exact (RelCT.seq (two_post (search_candidate_run_ct v) (candidate_ready v)) search_classify_ct).mono
      (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)

theorem search_iteration_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (iteration (candidateCode v)) (fun _ _ => True) := by
  unfold iteration
  change RelCT isa _ (.seq _ (.seq _ _)) _
  refine RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) remaining_ready) ?_
  exact RelCT.seq (two_post (branch_ct v) (branch_ready v))
    (two_taint [.r12] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_result_r12 h₁).trans (branch_result_r12 h₂).symm) (by taint_decide))

end VG.Proof.Ffdh.X86_64.Generation
