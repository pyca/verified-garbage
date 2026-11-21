module

public import VerifiedGarbage.Proof.Sm4.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4-CTR on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ctr
    verified := Proof.Sm4.Arm.Fn.ctr },
  Spec.Sm4.ctrFinalApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ctrFinal
    verified := Proof.Sm4.Arm.Fn.ctrFinal }]

end VG.Artifacts.Sm4Ctr.Arm
