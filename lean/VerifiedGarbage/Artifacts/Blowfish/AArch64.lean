module

public import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact AArch64.target {
    consts := Impl.Blowfish.AArch64.initConsts
    code := Impl.Blowfish.AArch64.expandKey
    verified := Proof.Blowfish.AArch64.expandKey_verified },
  Spec.Blowfish.ecbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.encrypt
    stack := 256
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.decrypt
    stack := 256
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.decrypt_verified }]

end VG.Artifacts.Blowfish.AArch64
