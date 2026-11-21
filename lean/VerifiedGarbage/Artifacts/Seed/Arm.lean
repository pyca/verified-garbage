module

public import VerifiedGarbage.Proof.Seed.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SEED on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Seed.Arm

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.expandKey
    verified := Proof.Seed.Arm.Fn.expandKey },
  Spec.Seed.ecbEncryptApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ecbEncrypt
    verified := Proof.Seed.Arm.Fn.ecbEncrypt },
  Spec.Seed.ecbDecryptApi.artifact Arm.target {
    code := Impl.Seed.Arm.Fn.ecbDecrypt
    verified := Proof.Seed.Arm.Fn.ecbDecrypt }]

end VG.Artifacts.Seed.Arm
