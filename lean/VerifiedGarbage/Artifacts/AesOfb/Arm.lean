module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.Arm

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact Arm.target Proof.Aes.Arm.Scrub.ofbReg,
  Spec.Ofb.aesFinalApi.artifact Arm.target Proof.Aes.Arm.Scrub.ofbFinalReg]

end VG.Artifacts.AesOfb.Arm
