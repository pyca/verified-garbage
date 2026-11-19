module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES (FIPS 197) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Aes.Arm

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact Arm.target Proof.Aes.Arm.Scrub.expandKeyReg]

end VG.Artifacts.Aes.Arm
