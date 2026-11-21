module

public import VerifiedGarbage.Proof.AesSiv.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-SIV (RFC 5297) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.Arm

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact Arm.target {
    code := Impl.AesSiv.Arm.Fn.init
    verified := Proof.AesSiv.Arm.Fn.init },
  Spec.Siv.encryptApi.artifact Arm.target {
    code := Impl.AesSiv.Arm.Fn.encrypt
    verified := Proof.AesSiv.Arm.Fn.encrypt },
  Spec.Siv.decryptApi.artifact Arm.target {
    code := Impl.AesSiv.Arm.Fn.decrypt
    verified := Proof.AesSiv.Arm.Fn.decrypt }]

end VG.Artifacts.AesSiv.Arm
