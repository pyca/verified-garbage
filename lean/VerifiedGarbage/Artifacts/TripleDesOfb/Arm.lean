module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.ofbReg,
  Spec.TripleDes.ofbFinalApi.artifact Arm.target Proof.TripleDes.Arm.Scrub.ofbFinalReg]

end VG.Artifacts.TripleDesOfb.Arm
