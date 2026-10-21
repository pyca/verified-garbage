module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.QOdd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidateQOdd_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s fun t =>
      CandidateContext p used t ∧ t.z=decide (((p.candidate-1)/2)%2=1) ∧
      t.mem=s.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (qOdd_ok h.read_context (by rw [number]; exact p.candidate_odd)) ?_
  rintro t ⟨flag,memory,rest⟩
  rw [number] at flag
  exact ⟨h.after_memory memory rest,flag,memory,rest.mono (by simp [roundClobbers])⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
