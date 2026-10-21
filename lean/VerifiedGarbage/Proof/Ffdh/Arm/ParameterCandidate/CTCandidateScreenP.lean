module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateScreenQ
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
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateSieve

/-! Initialize the shared RSA table and screen p using only public candidate data. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate

private def PSieveStart (p : CandidateParams) (s : State) : Prop :=
  CandidateSieveStart false ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private def PSieveEnd (p : CandidateParams) (s : State) : Prop :=
  CandidateSieved false ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private theorem pTable_ok (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s (PSieveStart p) := by
  refine WP.mono (candidateTable_ok h.context) ?_
  rintro t ⟨ctx, table, changed, _⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, p.candidate_odd⟩, h.enough⟩

theorem candidateScreenP_ct (v : RoundImpl) : RelCT isa (Two ScreenPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code) (fun _ _ => True) := by
  have table : RelCT isa (Two ScreenPStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite)
      (Two PSieveStart) :=
    two_post (two_map (fun p => (p, p.length)) (fun _ _ h => h.context) tableWrite_ct) pTable_ok
  have sieve : RelCT isa (Two PSieveStart) VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (Two PSieveEnd) :=
    two_post ((two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1)
      (candidateSieve_ct false)).mono (fun _ _ h => h) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (candidateSieved_ok false _ _ h.1) (fun _ post => ⟨post, h.2⟩))
  have branch : RelCT isa (Two PSieveEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.1.zero, right.1.zero]
    · exact two_map id (fun _ _ h => ⟨h.1.1.start.context, h.1.2, h.1.1.start.table, h.1.1.start.number⟩)
        (candidateScreenQ_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.1.start.context) candidateRejected_ct
  exact table.seq (sieve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
