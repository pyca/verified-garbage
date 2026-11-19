module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDes.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.expandKeyReg,
  Spec.TripleDes.ecbEncryptApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.ecbEncryptReg,
  Spec.TripleDes.ecbDecryptApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.ecbDecryptReg]

end VG.Artifacts.TripleDes.Arm
