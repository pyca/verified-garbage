module

public import VerifiedGarbage.Proof.Rc2.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # RC2 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc2.Arm

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact Arm.target Proof.Rc2.Arm.Scrub.cbcInitReg,
  Spec.Rc2.cbcEncryptChainedApi.artifact Arm.target Proof.Rc2.Arm.Scrub.cbcEncryptChainedReg,
  Spec.Rc2.cbcDecryptChainedApi.artifact Arm.target Proof.Rc2.Arm.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.Rc2.Arm
