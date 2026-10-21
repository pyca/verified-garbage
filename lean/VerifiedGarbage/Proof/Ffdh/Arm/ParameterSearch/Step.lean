module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Classify
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LiveGuards
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! One native search step calls a candidate only when the entropy suffix can hold its modulus. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.step (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep (.call backend.candidateName backend.candidate)) s
      fun t => Classified p used remaining t ∧ Rest searchClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep
  refine WP.seq (WP.mono h.length_guard fun u ⟨⟨live, flag, _⟩, rest⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro short
    have short' := of_decide_eq_true short
    have noCandidate := candidate_short p used short'
    have entropy : p.c.bytes.length - used < Spec.Ffdh.parameterEntropy p.c.bits := by
      have width := p.width_bounds
      unfold Spec.Ffdh.parameterEntropy
      change p.c.bytes.length - used < 32769 * p.c.length
      omega
    refine WP.mono live.short_request ?_
    rintro t ⟨done, restT⟩
    refine ⟨?_, (rest.mono (by simp [searchClobbers])).trans restT⟩
    simpa only [Classified, noCandidate, p.tail_short positive noCandidate,
      ite_eq_right (by omega : ¬ Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.bytes.length - used), requestResult] using done
  · intro enough
    have room : used + p.c.length ≤ p.c.bytes.length := by
      have := of_decide_eq_false enough
      have := h.usedBound
      omega
    refine WP.seq (WP.mono (candidateRun_ok backend live room) fun v ⟨⟨liveV, post⟩, restV⟩ => ?_)
    refine WP.mono (liveV.classify positive post) ?_
    rintro t ⟨data, restT⟩
    exact ⟨data, ((rest.mono (by simp [searchClobbers])).trans restV).trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
