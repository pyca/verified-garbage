module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CandidateFacts
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Advance
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Status
import VerifiedGarbage.Proof.Framework.Block

/-! Complete native rejection: advance entropy, subtract one u64 attempt and continue. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem SearchLive.reject {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) (post : CandidatePost p used s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.reject) s fun t =>
      (SearchLive p (used + candidateUsed p used) (remaining - 1) t ∧
        lowWord t.mem p.control 13 = 4#32) ∧ Rest [.r9, .r10, .r11, .r12] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.reject
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (h.reject_head (candidateUsed_bound p used) post.consumed_low) ?_
  rintro u ⟨liveU, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (liveU.decrement positive) ?_
  rintro v ⟨liveV, restV⟩
  refine WP.mono liveV.again ?_
  rintro t ⟨⟨live, status⟩, restT⟩
  exact ⟨⟨live, status⟩, (restU.trans (restV.mono (by simp))).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
