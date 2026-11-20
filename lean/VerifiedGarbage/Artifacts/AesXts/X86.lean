module

public import VerifiedGarbage.Proof.AesXts.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86

open VG.Proof.AesXts.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact X86.target (encryptUnitReg v),
    Spec.Xts.aesDecryptUnitApi.artifact X86.target (decryptUnitReg v)]

end VG.Artifacts.AesXts.X86
