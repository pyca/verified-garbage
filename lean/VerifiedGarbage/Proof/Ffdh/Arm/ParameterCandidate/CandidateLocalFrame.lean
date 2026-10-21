module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Each candidate-local store fits the controller's explicitly permitted state range. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

theorem candidate_local_frame {s t : State} {p : CandidateParams} {consumed d : Nat}
    (h : CandidateContext p consumed s) (lower : 40 ≤ d) (upper : d + 4 ≤ 68)
    (changed : Frame [⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩] s.mem t.mem) :
    Frame (candidateRegions p s.sp) s.mem t.mem := by
  refine changed.sub ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], ?_⟩
  rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
  exact Offset.sub _ lower (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
