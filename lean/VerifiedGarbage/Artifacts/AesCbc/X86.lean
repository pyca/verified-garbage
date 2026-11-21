module

public import VerifiedGarbage.Impl.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.AesCbc.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.X86

open VG.Proof.AesCbc.X86.Scrub

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Cbc.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.Fn.encrypt (Proof.AesCbc.X86.Wiped.encryptCode v) v.suffix (Proof.AesCbc.X86.Wiped.encWritten v)
      verified := Proof.AesCbc.X86.Scrub.encrypt_scrubbed v
      spSafe := Proof.AesCbc.X86.Scrub.encrypt_fnSpSafe v },
    Spec.Cbc.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.Fn.decrypt (Proof.AesCbc.X86.Wiped.decryptCode v) v.suffix (Proof.AesCbc.X86.Wiped.decWritten v)
      verified := Proof.AesCbc.X86.Scrub.decrypt_scrubbed v
      spSafe := Proof.AesCbc.X86.Scrub.decrypt_fnSpSafe v }]

end VG.Artifacts.AesCbc.X86
