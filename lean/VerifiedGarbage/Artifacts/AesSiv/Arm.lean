module

public import VerifiedGarbage.Proof.AesSiv.Arm.Frame
public import VerifiedGarbage.Proof.AesSiv.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-SIV (RFC 5297) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.Arm

open VG.Proof.AesSiv.Arm

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesSiv.Arm.init
    stack := 2568
    verified := init_framed },
  Spec.Siv.encryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.encrypt
    stack := 2624
    verified := Proof.AesSiv.encrypt_keyed encrypt_framed },
  Spec.Siv.decryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.decrypt
    stack := 2624
    verified := Proof.AesSiv.decrypt_keyed decrypt_framed }]

end VG.Artifacts.AesSiv.Arm
