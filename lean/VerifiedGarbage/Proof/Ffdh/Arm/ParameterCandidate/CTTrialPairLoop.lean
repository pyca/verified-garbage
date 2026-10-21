module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialLoopWord
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialWordCongr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! One public byte-count trace computes both exact sieve accumulators. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure TrialPairLoopPair (s t : State) : Prop extends TrialLoopPair s t where
  offset : s.gpr .r8=t.gpr .r8

private theorem trialPairLoop_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r0,.r1])
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairStep .ne) hint).isSome=true := ⟨_,by taint_decide⟩

theorem trialPairLoop_ct : RelCT isa TrialPairLoopPair
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairStep .ne)
    (fun s t => s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ s.gpr .r8=t.gpr .r8) := by
  obtain ⟨hint,checked⟩ := trialPairLoop_taint
  have trace : RelCT isa TrialPairLoopPair
      (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairStep .ne) (fun _ _ => True) := by
    refine RelCT.taint (A:=taint) (Taint.ofRegs [.r0,.r1]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro reg hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.pointer
    · exact h.count
  intro s t trS trT u v h runS runT
  have countS : s.gpr .r1=BitVec.ofNat 32 (s.gpr .r1).toNat := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have countT : t.gpr .r1=BitVec.ofNat 32 (s.gpr .r1).toNat := h.count.symm.trans countS
  obtain ⟨_,u',execS,valueAS,valueBS,_,restS⟩ :=
    trialPairLoopWord_ok s h.positive (s.gpr .r1).isLt countS h.readLeft
  obtain ⟨_,v',execT,valueAT,valueBT,_,restT⟩ :=
    trialPairLoopWord_ok t h.positive (s.gpr .r1).isLt countT h.readRight
  obtain ⟨_,rfl⟩ := Exec.det runS execS
  obtain ⟨_,rfl⟩ := Exec.det runT execT
  refine ⟨(trace _ _ _ _ _ _ h runS runT).1,?_,?_,?_⟩
  · rw [valueAS,valueAT,←h.pointer,←h.acc,←h.divisor,←h.inverse]
    exact trialWordResult_congr _ h.bytes
  · exact (restS.gpr .r3 (by simp)).trans (h.divisor.trans (restT.gpr .r3 (by simp)).symm)
  · rw [valueBS,valueBT,←h.pointer,←h.offset,←h.divisor,←h.inverse]
    exact trialWordResult_congr _ h.bytes

end VG.Proof.Ffdh.Arm.ParameterCandidate
