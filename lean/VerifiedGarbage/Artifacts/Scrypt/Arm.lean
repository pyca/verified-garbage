module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # scrypt (RFC 7914) on ARMv7 -/

namespace VG.Artifacts.Scrypt.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Scrypt.scryptApi.artifact Arm.target {
    code := Impl.Scrypt.Arm.Fn.scrypt
    verified := Proof.Scrypt.Arm.Fn.scrypt }]

spec_apis artifacts

end VG.Artifacts.Scrypt.Arm
