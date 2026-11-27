module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Impl.AesCbc.X86.Wiped
import VerifiedGarbage.Proof.AesCbc.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

namespace VG.Artifacts.AesCbc.X86

open VG.Proof.AesCbc.X86.Scrub

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Cbc.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.Fn.encrypt (Proof.AesCbc.X86.Wiped.encryptCode v) v.suffix (Proof.AesCbc.X86.Wiped.encWritten v)
      verified := Proof.AesCbc.X86.Scrub.encrypt_scrubbed v
      publicOutOk := Proof.AesCbc.X86.Scrub.encrypt_public v
      spSafe := Proof.AesCbc.X86.Scrub.encrypt_fnSpSafe v },
    Spec.Cbc.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCbc.X86.Fn.decrypt (Proof.AesCbc.X86.Wiped.decryptCode v) v.suffix (Proof.AesCbc.X86.Wiped.decWritten v)
        (Proof.AesCbc.X86.Wiped.decStack v)
      verified := Proof.AesCbc.X86.Scrub.decrypt_scrubbed v
      publicOutOk := Proof.AesCbc.X86.Scrub.decrypt_public v
      spSafe := Proof.AesCbc.X86.Scrub.decrypt_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesCbc.X86
