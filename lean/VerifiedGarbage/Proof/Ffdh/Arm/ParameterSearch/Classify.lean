module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CandidateFacts
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CompareResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Accept
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Reject
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Short
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Result
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The native classifier dispatches exactly the shared candidate's three possible results. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

def Classified (p : SearchParams) (used remaining : Nat) (s : State) : Prop :=
  match candidateResult p used with
  | some (none, _) => SearchLive p (used + candidateUsed p used) (remaining - 1) s ∧
      lowWord s.mem p.control 13 = 4#32
  | _ => SearchDone p (p.tail used remaining) s

theorem SearchLive.classify {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (positive : 0 < remaining) (post : CandidatePost p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.classify s fun t =>
      Classified p used remaining t ∧ Rest searchClobbers s t := by
  have small : Spec.Ffdh.candidateStatus (candidateResult p used) < 3 := by
    cases candidateResult p used with
    | none => decide
    | some pair =>
      obtain ⟨prime, rand⟩ := pair
      cases prime <;> simp only [Spec.Ffdh.candidateStatus] <;> decide
  have native : s.gpr .r0 = BitVec.ofNat 32 (Spec.Ffdh.candidateStatus (candidateResult p used)) := by
    rw [← post.status, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.classify
  refine WP.seq (WP.mono (compareResult_ok s small (Or.inl rfl) native) fun u ⟨⟨flag, mem⟩, rest⟩ => ?_)
  have liveU := h.after_read (by decide) mem rest
  have postU := post.after_read mem rest (by decide)
  have nativeU := (rest.gpr .r0 (by simp)).trans native
  cases result : candidateResult p used with
  | none =>
    simp only [result, Spec.Ffdh.candidateStatus] at flag
    refine WP.ite false (by change some u.z = _; rw [flag]; rfl) (by intro bad; cases bad) ?_
    intro _
    refine WP.seq (WP.mono (compareResult_ok u small (Or.inr rfl) nativeU) fun v ⟨⟨flagV, memV⟩, restV⟩ => ?_)
    have liveV := liveU.after_read (by decide) memV restV
    have postV := postU.after_read memV restV (by decide)
    simp only [result, Spec.Ffdh.candidateStatus] at flagV
    refine WP.ite false (by change some v.z = _; rw [flagV]; rfl) (by intro bad; cases bad) ?_
    intro _
    have zero := postV.output
    rw [result] at zero
    refine WP.mono (liveV.short positive result zero) ?_
    rintro t ⟨done, restT⟩
    exact ⟨by simpa only [Classified, result] using done,
      ((rest.trans restV).mono (by simp)).trans restT⟩
  | some pair =>
    obtain ⟨prime, rand⟩ := pair
    cases prime with
    | none =>
      simp only [result, Spec.Ffdh.candidateStatus] at flag
      refine WP.ite false (by change some u.z = _; rw [flag]; rfl) (by intro bad; cases bad) ?_
      intro _
      refine WP.seq (WP.mono (compareResult_ok u small (Or.inr rfl) nativeU) fun v ⟨⟨flagV, memV⟩, restV⟩ => ?_)
      have liveV := liveU.after_read (by decide) memV restV
      have postV := postU.after_read memV restV (by decide)
      simp only [result, Spec.Ffdh.candidateStatus] at flagV
      refine WP.ite true (by change some v.z = _; rw [flagV]; rfl) ?_ (by intro bad; cases bad)
      intro _
      refine WP.mono (liveV.reject positive postV) ?_
      rintro t ⟨data, restT⟩
      exact ⟨by simpa only [Classified, result] using data,
        ((rest.trans restV).mono (by simp)).trans (restT.mono (by simp [searchClobbers]))⟩
    | some prime =>
      simp only [result, Spec.Ffdh.candidateStatus] at flag
      refine WP.ite true (by change some u.z = _; rw [flag]; rfl) ?_ (by intro bad; cases bad)
      intro _
      refine WP.mono (liveU.accept postU result) ?_
      rintro t ⟨done, restT⟩
      refine ⟨?_, (rest.mono (by simp)).trans (restT.mono (by simp [searchClobbers]))⟩
      simpa only [Classified, result, p.tail_accept positive result] using done

end VG.Proof.Ffdh.Arm.ParameterSearch
