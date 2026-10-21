module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialWordCongr
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Trial division has a public byte-count trace and retains an equal public accumulator. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure TrialLoopPair (s t : State) : Prop where
  pointer : s.gpr .r0 = t.gpr .r0
  count : s.gpr .r1 = t.gpr .r1
  acc : s.gpr .r2 = t.gpr .r2
  divisor : s.gpr .r3 = t.gpr .r3
  inverse : s.gpr .r4 = t.gpr .r4
  positive : 0 < (s.gpr .r1).toNat
  readLeft : TrialReadable s (s.gpr .r0) (s.gpr .r1).toNat
  readRight : TrialReadable t (t.gpr .r0) (s.gpr .r1).toNat
  bytes : ∀ i < (s.gpr .r1).toNat,
    s.mem (State.addr (s.gpr .r0 - BitVec.ofNat 32 (i + 1))) =
      t.mem (State.addr (s.gpr .r0 - BitVec.ofNat 32 (i + 1)))

theorem trialLoop_ct : RelCT isa TrialLoopPair
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) (fun s t => s.gpr .r2 = t.gpr .r2) := by
  obtain ⟨hint, checked⟩ := trialLoop_taint
  have trace : RelCT isa TrialLoopPair (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.pointer
    · exact h.count
  intro s t trS trT u v h runS runT
  have countS : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have countT : t.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := h.count.symm.trans countS
  obtain ⟨_, u', execS, valueS, _, _⟩ := trialLoopWord_ok s h.positive (s.gpr .r1).isLt countS h.readLeft
  obtain ⟨_, v', execT, valueT, _, _⟩ := trialLoopWord_ok t h.positive (s.gpr .r1).isLt countT h.readRight
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  refine ⟨(trace _ _ _ _ _ _ h runS runT).1, ?_⟩
  change u.gpr .r2 = v.gpr .r2
  rw [valueS, valueT]
  rw [← h.pointer, ← h.acc, ← h.divisor, ← h.inverse]
  exact trialWordResult_congr _ h.bytes

end VG.Proof.Ffdh.Arm.ParameterCandidate
