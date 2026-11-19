module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-CTR on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact Arm.target Proof.Camellia.Arm.Scrub.ctrReg,
  Spec.Camellia.ctrFinalApi.artifact Arm.target Proof.Camellia.Arm.Scrub.ctrFinalReg]

end VG.Artifacts.CamelliaCtr.Arm
