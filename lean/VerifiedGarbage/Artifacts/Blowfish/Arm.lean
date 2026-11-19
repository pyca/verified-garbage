module

public import VerifiedGarbage.Proof.Blowfish.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Blowfish on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 96 .r3 20 Impl.Blowfish.Arm.expandKey
    verified := .unscrubbed Proof.Blowfish.Arm.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 20 Impl.Blowfish.Arm.encrypt
    verified := .unscrubbed (Proof.Blowfish.Arm.ecb_framed true) },
  Spec.Blowfish.ecbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 20 Impl.Blowfish.Arm.decrypt
    verified := .unscrubbed (Proof.Blowfish.Arm.ecb_framed false) }]

end VG.Artifacts.Blowfish.Arm
