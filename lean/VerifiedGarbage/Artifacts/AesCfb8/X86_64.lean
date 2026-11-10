module

public import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
public import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.X86_64


def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) => [
    Spec.Cfb8.aesEncryptApi.artifact X86_64.target (Proof.Aes.X86_64.ModesScrub.cfb8EncryptReg v),
    Spec.Cfb8.aesDecryptApi.artifact X86_64.target (Proof.Aes.X86_64.ModesScrub.cfb8DecryptReg v)]

end VG.Artifacts.AesCfb8.X86_64
