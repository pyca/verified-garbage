module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSpec
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMain
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete candidate control flow, including the short initial entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateGuard_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)]) s
      (CandidateReturn p (candidateAnswer p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (initialRoom_ok h.saved.space p.tapeCount
    (by have := p.length_bounds; omega) (h.saved.saved 20 (by decide)) (h.saved.saved 12 (by decide))) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases enough : p.length ≤ p.bytes.length
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false (by omega)]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateMain_ok v ctx enough) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateAnswer, ite_eq_left enough]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (by simp [roundClobbers])
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true (by omega)]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateNone_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateAnswer, ite_eq_right enough]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (by simp [roundClobbers])

end VG.Proof.Ffdh.Arm.ParameterCandidate
