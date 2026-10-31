module

public import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CTR artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ctr
    stack := 2904
    verified := Proof.Camellia.Arm.ctr_framed }]

end VG.Artifacts.CamelliaCtr.Arm
