module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofb
    stack := 320
    verified := Proof.Blowfish.Arm.ofb_framed }]

end VG.Artifacts.BlowfishOfb.Arm
