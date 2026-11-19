module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Camellia.Arm

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact Arm.target Proof.Camellia.Arm.Scrub.expandKeyReg,
  Spec.Camellia.ecbEncryptApi.artifact Arm.target Proof.Camellia.Arm.Scrub.ecbEncryptReg,
  Spec.Camellia.ecbDecryptApi.artifact Arm.target Proof.Camellia.Arm.Scrub.ecbDecryptReg]

end VG.Artifacts.Camellia.Arm
