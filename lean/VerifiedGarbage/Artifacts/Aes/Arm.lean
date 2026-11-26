module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES (FIPS 197) on ARMv7 -/

namespace VG.Artifacts.Aes.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Aes.expandKeyApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.expandKey
    verified := Proof.Aes.Arm.Fn.expandKey }]

spec_apis artifacts

end VG.Artifacts.Aes.Arm
