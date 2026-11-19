module

public import VerifiedGarbage.Proof.ChaCha20.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # ChaCha20 (RFC 8439) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact Arm.target Proof.ChaCha20.Arm.Scrub.initReg,
  Spec.ChaCha20.setNonceApi.artifact Arm.target Proof.ChaCha20.Arm.Scrub.setNonceReg,
  Spec.ChaCha20.applyApi.artifact Arm.target Proof.ChaCha20.Arm.Scrub.applyReg]

end VG.Artifacts.ChaCha20.Arm
