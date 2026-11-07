module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.Arm

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCtr.ctr
    stack := 1520
    verified := Proof.Sm4.Arm.BatchVerified.framed },
  Spec.Sm4.ctrFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Sm4.Arm.ctrFinal
    stack := 1584
    verified := Proof.Sm4.Arm.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.Sm4Ctr.Arm
