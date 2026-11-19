module

public import VerifiedGarbage.Proof.Scrypt.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # scrypt (RFC 7914) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List Artifact := [
  Spec.Scrypt.scryptApi.artifact Arm.target Proof.Scrypt.Arm.Scrub.scryptReg]

end VG.Artifacts.Scrypt.Arm
