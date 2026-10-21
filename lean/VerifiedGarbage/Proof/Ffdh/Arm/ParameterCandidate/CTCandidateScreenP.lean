module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateScreenPair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateQOdd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTQOdd
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Reject even q before the paired RSA trial sieve and shared witness controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length≤p.bytes.length
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate

private structure QOddChecked (p : CandidateParams) (s : State) : Prop where
  start : ScreenPStart p s
  zero : s.z=decide (((p.candidate-1)/2)%2=1)

private theorem qOdd_checked (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s (QOddChecked p) := by
  refine WP.mono (candidateQOdd_ok h.context h.number) ?_
  rintro t ⟨ctx,zero,memory,_⟩
  exact ⟨⟨ctx,h.enough,by rw [memory]; exact h.number⟩,zero⟩

theorem candidateScreenP_ct (v : RoundImpl) : RelCT isa (Two ScreenPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code) (fun _ _ => True) := by
  have guard : RelCT isa (Two ScreenPStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) (Two QOddChecked) :=
    two_post ((two_map (fun p => (p.out,p.length)) (fun _ _ h => h.context.read_context) qOdd_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) qOdd_checked
  have branch : RelCT isa (Two QOddChecked)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite ?_ ?_ ?_
    · intro p s t a b
      change some s.z=some t.z
      rw [a.zero,b.zero]
    · refine two_map id ?_ (candidateScreenPair_ct v)
      intro p s h
      refine ⟨h.1.start.context,h.1.start.enough,?_,h.1.start.number⟩
      apply of_decide_eq_true
      have go : some s.z=some true := h.2
      exact h.1.zero.symm.trans (Option.some.inj go)
    · exact two_map (fun p => (⟨p,p.length⟩ : CandidatePoint))
        (fun _ _ h => h.1.start.context) candidateRejected_ct
  exact guard.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
