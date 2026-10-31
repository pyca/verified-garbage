module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CFB8 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfb8Encrypt
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfb8Encrypt_framed },
  Spec.TripleDes.cfb8DecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.cfb8Decrypt
    stack := 1008
    verified := Proof.TripleDes.AArch64.cfb8Decrypt_framed }]

end VG.Artifacts.TripleDesCfb8.AArch64
