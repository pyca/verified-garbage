module

public import VerifiedGarbage.Proof.Sm4.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4-OFB on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ofb
    verified := Proof.Sm4.Arm.Fn.ofb },
  Spec.Sm4.ofbFinalApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ofbFinal
    verified := Proof.Sm4.Arm.Fn.ofbFinal }]

end VG.Artifacts.Sm4Ofb.Arm
