module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDrawSample
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT

/-! Sampling and the shared full-width witness range check have public traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

private def SampleReady (p : DrawPoint) (s : State) : Prop :=
  ArithmeticReady p.params.base p.params.capacity p.params.words s

theorem drawRange_ct : RelCT isa (Two DrawStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange (fun _ _ => True) := by
  have sample : RelCT isa (Two DrawStart) VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample (Two SampleReady) :=
    two_post drawSample_ct (fun _ _ h => WP.mono (drawSample_ok h.1 h.2) (fun _ post => post.2.1))
  refine sample.seq ?_
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact VG.Proof.Ffdh.Arm.inRange_ct (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Spec.Rsa.Mont.Operand 1) (by decide : 1 ≠ 7)
    _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
