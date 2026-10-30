module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb
    stack := 1088
    verified := Proof.TripleDes.Arm.ofb_framed }]

end VG.Artifacts.TripleDesOfb.Arm
