module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact Arm.target Proof.Camellia.Arm.Scrub.ofbReg,
  Spec.Camellia.ofbFinalApi.artifact Arm.target Proof.Camellia.Arm.Scrub.ofbFinalReg]

end VG.Artifacts.CamelliaOfb.Arm
