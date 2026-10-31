module

public import VerifiedGarbage.Proof.Blowfish.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact Arm.target {
    consts := Impl.Blowfish.Arm.initConsts
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 12 Impl.Blowfish.Arm.expandKey
    stack := 64
    verified := Proof.Blowfish.Arm.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 Impl.Blowfish.Arm.encrypt
    stack := 256
    verified := Proof.Blowfish.Arm.ecb_framed true },
  Spec.Blowfish.ecbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 Impl.Blowfish.Arm.decrypt
    stack := 256
    verified := Proof.Blowfish.Arm.ecb_framed false }]

end VG.Artifacts.Blowfish.Arm
