module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ofb
    verified := Proof.Camellia.Arm.Fn.ofb },
  Spec.Camellia.ofbFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ofbFinal
    verified := Proof.Camellia.Arm.Fn.ofbFinal }]

end VG.Artifacts.CamelliaOfb.Arm
