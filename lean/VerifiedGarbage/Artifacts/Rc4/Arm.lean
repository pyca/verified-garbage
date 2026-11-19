module

public import VerifiedGarbage.Proof.Rc4.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # RC4 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc4.Arm

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact Arm.target Proof.Rc4.Arm.Scrub.initReg,
  Spec.Rc4.applyApi.artifact Arm.target Proof.Rc4.Arm.Scrub.applyReg]

end VG.Artifacts.Rc4.Arm
