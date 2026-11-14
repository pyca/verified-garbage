module

public import VerifiedGarbage.Proof.Aes.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES (FIPS 197) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Aes.Arm

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey
    stack := 512
    verified := Proof.Aes.Arm.expandKey_framed }]

end VG.Artifacts.Aes.Arm
