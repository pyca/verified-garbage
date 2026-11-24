module

public import VerifiedGarbage.Proof.Seed.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # SEED-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cbcEncrypt
    verified := Proof.Seed.Arm.Fn.cbcEncrypt },
  Spec.Seed.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.cbcDecrypt
    verified := Proof.Seed.Arm.Fn.cbcDecrypt }]

end VG.Artifacts.SeedCbc.Arm
