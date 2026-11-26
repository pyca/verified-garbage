module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-SIV (RFC 5297) on ARMv7 -/

namespace VG.Artifacts.AesSiv.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Siv.initApi.artifact Arm.target {
    code := Impl.AesSiv.Arm.Fn.init
    verified := Proof.AesSiv.Arm.Fn.init },
  Spec.Siv.encryptApi.artifact Arm.target {
    code := Impl.AesSiv.Arm.Fn.encrypt
    verified := Proof.AesSiv.Arm.Fn.encrypt },
  Spec.Siv.decryptApi.artifact Arm.target {
    code := Impl.AesSiv.Arm.Fn.decrypt
    verified := Proof.AesSiv.Arm.Fn.decrypt }]

spec_apis artifacts

end VG.Artifacts.AesSiv.Arm
