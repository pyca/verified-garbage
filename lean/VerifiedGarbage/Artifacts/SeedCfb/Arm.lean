module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
import VerifiedGarbage.Proof.Seed.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CFB128 on ARMv7 -/

namespace VG.Artifacts.SeedCfb.Arm

public def artifacts : List (Artifact Arm.target) := [
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

spec_apis artifacts

end VG.Artifacts.SeedCfb.Arm
