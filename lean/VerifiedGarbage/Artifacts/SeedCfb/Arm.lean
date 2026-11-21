module

public import VerifiedGarbage.Proof.Seed.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SEED-CFB128 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.Arm

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cfbEncrypt
    verified := Proof.Seed.Arm.Fn.cfbEncrypt },
  Spec.Seed.cfbDecryptApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cfbDecrypt
    verified := Proof.Seed.Arm.Fn.cfbDecrypt },
  Spec.Seed.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cfbEncryptFinal
    verified := Proof.Seed.Arm.Fn.cfbEncryptFinal },
  Spec.Seed.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cfbDecryptFinal
    verified := Proof.Seed.Arm.Fn.cfbDecryptFinal }]

end VG.Artifacts.SeedCfb.Arm
