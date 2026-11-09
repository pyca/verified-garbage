module

public import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
public import VerifiedGarbage.Proof.Camellia.Arm.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ctr
    stack := 2904
    verified := Proof.Camellia.Arm.ctr_framed },
  Spec.Camellia.ctrFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 Impl.Camellia.Arm.ctrFinal
    stack := 2984
    verified := Proof.Camellia.Arm.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.CamelliaCtr.Arm
