module

public import VerifiedGarbage.Proof.Camellia.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.Arm

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcEncryptChained
    stack := 2904
    verified := Proof.Camellia.Arm.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained
    stack := 2904
    verified := Proof.Camellia.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.Arm
