module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Input
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Correct
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Timing
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Sat
public import VerifiedGarbage.TCB.Arm.Target

/-! Standard-domain recognition and the complete general fallback are verified. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm

theorem verified : Verified target VG.Impl.Ffdh.Arm.VettedValidation.code contract :=
  ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.Arm.VettedValidation
