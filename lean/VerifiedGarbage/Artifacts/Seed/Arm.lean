module

public import VerifiedGarbage.Proof.Seed.Arm.KeyVerified
public import VerifiedGarbage.Proof.Seed.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Seed.Arm

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey
    stack := 752
    verified := Proof.Seed.Arm.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r3 188 (Impl.Seed.Arm.ecb .encrypt)
    stack := 752
    verified := Proof.Seed.Arm.ecb_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r3 188 (Impl.Seed.Arm.ecb .decrypt)
    stack := 752
    verified := Proof.Seed.Arm.ecb_framed .decrypt }]

end VG.Artifacts.Seed.Arm
