module

public import VerifiedGarbage.Proof.Seed.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.Arm

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncryptChained
    stack := 832
    verified := Proof.Seed.Arm.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecryptChained
    stack := 832
    verified := Proof.Seed.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.Arm
