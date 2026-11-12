module

public import VerifiedGarbage.Proof.AesXts.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesXts.X86_64

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesXts.X86_64.variants.flatMap fun (v : Proof.AesXts.X86_64.XtsImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact X86_64.target (Proof.AesXts.X86_64.Scrub.encryptUnitReg v),
    Spec.Xts.aesDecryptUnitApi.artifact X86_64.target (Proof.AesXts.X86_64.Scrub.decryptUnitReg v),
    Spec.Xts.aesEncryptUnitToApi.artifact X86_64.target (Proof.AesXts.X86_64.Scrub.encryptUnitToReg v),
    Spec.Xts.aesDecryptUnitToApi.artifact X86_64.target (Proof.AesXts.X86_64.Scrub.decryptUnitToReg v)]

end VG.Artifacts.AesXts.X86_64
