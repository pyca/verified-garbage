module

public import VerifiedGarbage.Proof.Seed.Arm.FbVerified
public import VerifiedGarbage.Proof.Seed.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Seed.Arm.FbFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SEED-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.Arm

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncrypt
    stack := 832
    verified := Proof.Seed.Arm.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecrypt
    stack := 832
    verified := Proof.Seed.Arm.cfbDecrypt_framed },
  Spec.Seed.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncryptFinal
    stack := 832
    verified := Proof.Seed.Arm.cfbEncryptFinal_framed },
  Spec.Seed.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecryptFinal
    stack := 832
    verified := Proof.Seed.Arm.cfbDecryptFinal_framed }]

end VG.Artifacts.SeedCfb.Arm
