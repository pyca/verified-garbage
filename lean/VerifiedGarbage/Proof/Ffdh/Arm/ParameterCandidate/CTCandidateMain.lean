module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateResidue
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTestP
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateCount
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateScreenP

/-! Complete native candidate controller timing from public entropy and buffer descriptors. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def CountedStart (p : CandidateParams) (s : State) : Prop :=
  CandidateContext p p.length s ∧ p.length ≤ p.bytes.length

private structure CandidateResidueEnd (p : CandidateParams) (s : State) : Prop where
  start : ScreenPStart p s
  zero : s.z = Spec.Ffdh.generationShape p.bits p.generator p.candidate

private theorem candidateResidueEnd_ok (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue s (CandidateResidueEnd p) := by
  refine WP.mono (candidateResidue_ok h.context h.number) ?_
  rintro t ⟨ctx, zero, mem, _⟩
  exact ⟨⟨ctx, h.enough, by rw [mem]; exact h.number⟩, zero⟩

theorem candidateMain_ct (v : RoundImpl) : RelCT isa (Two CandidateTestPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code) (fun _ _ => True) := by
  have countTrace : RelCT isa (fun s t => s.sp = t.sp)
      (.block (([.ldrSp .r1 12] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40))
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct [.ldrSp .r1 12] rfl).seq (save_ct .r1 40))
  have count : RelCT isa (Two CandidateTestPStart)
      (.block (([.ldrSp .r1 12] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40)) (Two CountedStart) :=
    (two_post (countTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
      (fun p _ h => WP.mono (candidateCount_ok h.1 h.2) (fun _ ⟨ctx, _, _⟩ => (show CountedStart p.params _ from ⟨ctx, h.2⟩)))).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.params, left, right, sp⟩)
  have shapeTrace : RelCT isa (Two CountedStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) :=
    two_map (fun p => (⟨p.out, p.tape, p.bytes.take p.length, p.bits⟩ : ShapeData)) (fun _ _ h => h.1.shape_context h.2) shapeP_ct
  have shape : RelCT isa (Two CountedStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (Two ScreenPStart) :=
    two_post shapeTrace (fun _ _ h => WP.mono (candidateShape_ok h.1 h.2) (fun _ ⟨ctx, _, number, _, _⟩ => ⟨ctx, h.2, number⟩))
  have residue : RelCT isa (Two ScreenPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.residue (Two CandidateResidueEnd) :=
    two_post candidateResidue_ct candidateResidueEnd_ok
  have branch : RelCT isa (Two CandidateResidueEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map id (fun _ _ h => h.1.start) (candidateScreenP_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.start.context) candidateRejected_ct
  exact count.seq (shape.seq (residue.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
