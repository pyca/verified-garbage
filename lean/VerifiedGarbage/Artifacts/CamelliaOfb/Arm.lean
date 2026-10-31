module

public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofb
    stack := 2904
    verified := Proof.Camellia.Arm.ofb_framed }]

end VG.Artifacts.CamelliaOfb.Arm
