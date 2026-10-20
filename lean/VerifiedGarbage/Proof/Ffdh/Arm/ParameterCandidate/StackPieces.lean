module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! Fixed candidate operations do not allocate additional stack frames. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Impl.Ffdh.Arm.ParameterCandidate

theorem shapeP_stack : FrameStack.armStack shapeP = 0 := by decide +kernel
theorem residue_stack : FrameStack.armStack residue = 0 := by decide +kernel
theorem sieve_stack : FrameStack.armStack sieve = 0 := by decide +kernel
theorem halveQ_stack : FrameStack.armStack halveQ = 0 := by decide +kernel
theorem finNone_stack : FrameStack.armStack finNone = 0 := by decide +kernel
theorem finRejected_stack : FrameStack.armStack finRejected = 0 := by decide +kernel
theorem result_stack : FrameStack.armStack result = 0 := by decide +kernel
theorem phasePrepared_stack : FrameStack.armStack phasePrepared = 0 := by decide +kernel
theorem drawRange_stack : FrameStack.armStack drawRange = 0 := by decide +kernel
theorem montEncode_stack : FrameStack.armStack (VG.Impl.Bignum.Arm.montOp 5 1 4) = 0 := by decide +kernel
theorem onPass_stack : FrameStack.armStack onPass = 0 := by decide +kernel

end VG.Proof.Ffdh.Arm.ParameterCandidate
