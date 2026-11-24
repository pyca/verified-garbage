module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # AES (FIPS 197) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Aes.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.Aes.expandKeyApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.expandKey
    verified := Proof.Aes.Arm.Fn.expandKey }]

end VG.Artifacts.Aes.Arm
