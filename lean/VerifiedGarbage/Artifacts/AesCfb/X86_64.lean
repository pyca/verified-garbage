module

public import VerifiedGarbage.Proof.AesCfb.X86_64.Verified
public import VerifiedGarbage.Proof.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
public import VerifiedGarbage.Proof.Aes.X86_64.FinalScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) => [
    Spec.Cfb.aesEncryptApi.artifact X86_64.target (Proof.Aes.X86_64.ModesScrub.cfbEncryptReg v),
    Spec.Cfb.aesDecryptApi.artifact X86_64.target (Proof.Aes.X86_64.ModesScrub.cfbDecryptReg v),
    Spec.Cfb.aesEncryptFinalApi.artifact X86_64.target (Proof.Aes.X86_64.FinalScrub.cfbEncryptFinalReg v),
    Spec.Cfb.aesDecryptFinalApi.artifact X86_64.target (Proof.Aes.X86_64.FinalScrub.cfbDecryptFinalReg v)]

end VG.Artifacts.AesCfb.X86_64
