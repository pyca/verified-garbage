module

public import VerifiedGarbage.Proof.AesCfb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.X86

open VG.Proof.AesCfb.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Cfb.aesEncryptApi.artifact X86.target (encryptReg v),
    Spec.Cfb.aesDecryptApi.artifact X86.target (decryptReg v),
    Spec.Cfb.aesEncryptFinalApi.artifact X86.target (encryptFinalReg v),
    Spec.Cfb.aesDecryptFinalApi.artifact X86.target (decryptFinalReg v)]

end VG.Artifacts.AesCfb.X86
