module

public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Camellia.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Camellia.Arm.FbFinal

/-! # Camellia-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofb
    stack := 2904
    verified := Proof.Camellia.Arm.ofb_framed },
  Spec.Camellia.ofbFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofbFinal
    stack := 2904
    verified := Proof.Camellia.Arm.ofbFinal_framed }]

end VG.Artifacts.CamelliaOfb.Arm
