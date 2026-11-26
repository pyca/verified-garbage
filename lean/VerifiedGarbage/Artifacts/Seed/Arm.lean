module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.Seed.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED on ARMv7 -/

namespace VG.Artifacts.Seed.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Seed.expandKeyApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.expandKey
    verified := Proof.Seed.Arm.Fn.expandKey },
  Spec.Seed.ecbEncryptApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ecbEncrypt
    verified := Proof.Seed.Arm.Fn.ecbEncrypt },
  Spec.Seed.ecbDecryptApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ecbDecrypt
    verified := Proof.Seed.Arm.Fn.ecbDecrypt }]

spec_apis artifacts

end VG.Artifacts.Seed.Arm
