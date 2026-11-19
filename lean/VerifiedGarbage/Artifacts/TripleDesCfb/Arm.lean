module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES-CFB64 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.cfbEncryptReg,
  Spec.TripleDes.cfbDecryptApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.cfbDecryptReg,
  Spec.TripleDes.cfbEncryptFinalApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.cfbEncryptFinalReg,
  Spec.TripleDes.cfbDecryptFinalApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.TripleDesCfb.Arm
