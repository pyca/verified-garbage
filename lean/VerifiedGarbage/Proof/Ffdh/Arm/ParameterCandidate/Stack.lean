module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.StackPieces
import VerifiedGarbage.Proof.Ffdh.Arm.CallerRows
import VerifiedGarbage.Proof.Framework.Omega

/-! The candidate frame and shared round require at most 184 bytes of stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

private theorem candidate_code_stack (name : String) (body : Prog isa) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.code name body) = FrameStack.armStack body + 128 := by
  have roundKernelStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack (VG.Impl.Bignum.Arm.montOp 5 1 4)) (max 0 (max (FrameStack.armStack body) 0)) = _
    rw [montEncode_stack, Nat.max_zero, Nat.zero_max, Nat.zero_max]
  have roundStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.round name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel name body)) (max 0 (max (max 0 (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.onPass)) 0)) = _
    rw [roundKernelStack, onPass_stack]
    simp only [Nat.max_self, Nat.max_zero]
  have drawStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.draw name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange) (max 0 (max (max 0 (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.round name body))) 0)) = _
    rw [drawRange_stack, roundStack]
    simp only [Nat.zero_max, Nat.max_zero]
  have stepStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep name body) = FrameStack.armStack body := by
    change max 0 (max (max 0 (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.draw name body))) 0) = _
    rw [drawStack]
    simp only [Nat.zero_max, Nat.max_zero]
  have testStack (q : Bool) : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.test q name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared)
      (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep name body))) = _
    rw [phasePrepared_stack, stepStack, Nat.zero_max, Nat.zero_max]
  have testsStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.tests name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.test true name body))
      (max 0 (max (max (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP)
        (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.test false name body))
          (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.result) 0)))
        (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.result)) 0)) = _
    rw [testStack true, testStack false, shapeP_stack, result_stack]
    simp only [Nat.zero_max, Nat.max_zero, Nat.max_self]
  have screenQStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ)
      (max (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)
        (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.sieve)
          (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.tests name body))
            (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)) 0))) 0) = _
    rw [halveQ_stack, finRejected_stack, sieve_stack, testsStack]
    simp only [Nat.zero_max, Nat.max_zero]
  have screenPStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.sieve)
      (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ name body))
        (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)) 0)) = _
    rw [sieve_stack, screenQStack, finRejected_stack]
    simp only [Nat.zero_max, Nat.max_zero]
  have mainStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.main name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP)
      (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.residue)
        (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP name body))
          (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)) 0))) = _
    rw [shapeP_stack, residue_stack, screenPStack, finRejected_stack]
    simp only [Nat.zero_max, Nat.max_zero]
  change max 0 (max 0 (max (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finNone)
    (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.main name body))) 0)) + 72 + 56 = _
  rw [finNone_stack, mainStack]
  simp only [Nat.zero_max, Nat.max_zero, Nat.add_assoc]

theorem candidate_stack (v : RoundImpl) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) ≤ 184 := by
  rw [candidate_code_stack]
  have := v.stack
  omega

theorem optimizedCandidate_stack (umaal : Bool) (v : RoundImpl) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.optimizedCode umaal v.name v.code) ≤ 184 := by
  cases umaal with
  | false => exact candidate_stack v
  | true => exact (VG.Proof.Ffdh.Arm.CallerRows.stack _).trans (candidate_stack v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
