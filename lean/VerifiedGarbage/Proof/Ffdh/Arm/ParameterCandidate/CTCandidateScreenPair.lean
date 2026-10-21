module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedTests
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidatePair

/-! The paired screening stage depends only on public candidate data. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPairStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  oddQ : ((p.candidate-1)/2)%2=1
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate

private def PSieveStart (p : CandidateParams) (s : State) : Prop :=
  CandidatePairStart ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private def PSieveEnd (p : CandidateParams) (s : State) : Prop :=
  CandidatePaired ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private theorem pTable_ok (p : CandidateParams) (s : State) (h : ScreenPairStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s (PSieveStart p) := by
  refine WP.mono (candidateTable_ok h.context) ?_
  rintro t ⟨ctx, table, changed, _⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.oddQ⟩, h.enough⟩

theorem candidateScreenPair_ct (v : RoundImpl) : RelCT isa (Two ScreenPairStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair v.name v.code) (fun _ _ => True) := by
  have table : RelCT isa (Two ScreenPairStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite)
      (Two PSieveStart) :=
    two_post (two_map (fun p => (p, p.length)) (fun _ _ h => h.context) tableWrite_ct) pTable_ok
  have sieve : RelCT isa (Two PSieveStart) VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (Two PSieveEnd) :=
    two_post ((two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1)
      (candidatePair_ct)).mono (fun _ _ h => h) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (candidatePaired_ok _ _ h.1) (fun _ post => ⟨post, h.2⟩))
  have branch : RelCT isa (Two PSieveEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.1.zero, right.1.zero]
    · exact two_map (fun p => (⟨p,p.length⟩ : CandidatePoint))
        (fun _ _ h => ⟨h.1.1.start.context,h.1.2,h.1.1.start.oddQ⟩) (screenedTests_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.1.start.context) candidateRejected_ct
  exact table.seq (sieve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
