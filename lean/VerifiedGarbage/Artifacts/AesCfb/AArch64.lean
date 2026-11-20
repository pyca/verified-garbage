module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Caller
public import VerifiedGarbage.Proof.AesCfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.AArch64.ModesScrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAllW
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.AesCfb.AArch64.Body
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.AArch64

open VG.Proof.AesCfb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Cfb.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.encrypt v.enc
      verified := .scrubbed (Final.encrypt_scrubbed v) },
    Spec.Cfb.aesDecryptApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAllW {
      suffix := v.suffix
      code := Caller.decrypt v
      verified := Proof.AesCfb.decrypt_keyed (Caller.verified v)
      written := Caller.written v
      writtenOk := Caller.written_ok v } Proof.Aes.AArch64.ModesScrub.cfbDecryptOk),
    Spec.Cfb.aesEncryptFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.encryptFinal v.enc v.suffix
      verified := .scrubbed (Final.encryptFinal_scrubbed v) },
    Spec.Cfb.aesDecryptFinalApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Final.decryptCode v)
      verified := Proof.AesCfb.decryptFinal_keyed (Final.decryptFinal_framed v) } Proof.Aes.AArch64.ModesScrub.cfbDecryptFinalOk)]

end VG.Artifacts.AesCfb.AArch64
