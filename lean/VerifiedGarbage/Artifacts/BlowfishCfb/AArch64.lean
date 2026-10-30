module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbEncrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cfbDecrypt
    stack := 224
    verified := Proof.Blowfish.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.BlowfishCfb.AArch64
