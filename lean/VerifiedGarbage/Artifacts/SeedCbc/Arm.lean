module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Proof.Seed.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CBC on ARMv7 -/

namespace VG.Artifacts.SeedCbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cbcEncrypt
    verified := Proof.Seed.Arm.Fn.cbcEncrypt },
  Spec.Seed.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cbcDecrypt
    verified := Proof.Seed.Arm.Fn.cbcDecrypt }]

spec_apis artifacts

end VG.Artifacts.SeedCbc.Arm
