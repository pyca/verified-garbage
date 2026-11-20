module

public import VerifiedGarbage.Proof.Blake2.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # BLAKE2s (RFC 7693) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.Arm

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact Arm.target Proof.Blake2.Arm.Scrub.initSReg,
  Spec.Blake2.updateSApi.artifact Arm.target Proof.Blake2.Arm.Scrub.updateSReg,
  Spec.Blake2.finalizeSApi.artifact Arm.target Proof.Blake2.Arm.Scrub.finalizeSReg]

end VG.Artifacts.Blake2s.Arm
