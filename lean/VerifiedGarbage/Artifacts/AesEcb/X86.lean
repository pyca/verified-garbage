module

public import VerifiedGarbage.Impl.AesEcb.X86
public import VerifiedGarbage.Proof.AesEcb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.X86

open VG.Proof.AesEcb.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.AesEcb.encryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesEcb.X86.Fn.crypt (ecbFree v.enc v.encWritten) v.enc v.encWritten
      verified := encrypt_scrubbed v
      spSafe := encrypt_fnSpSafe v },
    Spec.AesEcb.decryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesEcb.X86.Fn.crypt (ecbFree v.dec v.decWritten) v.dec v.decWritten
      verified := decrypt_scrubbed v
      spSafe := decrypt_fnSpSafe v }]

end VG.Artifacts.AesEcb.X86
