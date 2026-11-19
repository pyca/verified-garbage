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
  VG.Proof.Variants.AesBlocks.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Aes.AArch64.BlocksImpl // v ∈ VG.Proof.Variants.AesBlocks.AArch64.variants }) => [
    Spec.Cfb.aesEncryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesCfb.AArch64.encrypt v.1.enc
      verified := Proof.AesCfb.encrypt_keyed (encrypt_verified v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.cfbEncryptOwn v.1.encClear)
      Proof.Aes.AArch64.ModesScrub.cfbEncryptOk (Proof.Aes.AArch64.ModesScrub.cfbEncryptSide v.1 v.2)),
    Spec.Cfb.aesDecryptApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAllW {
      suffix := v.1.suffix
      code := Caller.decrypt v.1
      verified := Proof.AesCfb.decrypt_keyed (Caller.verified v.1)
      written := Caller.written v.1
      writtenOk := Caller.written_ok v.1 } Proof.Aes.AArch64.ModesScrub.cfbDecryptOk),
    Spec.Cfb.aesEncryptFinalApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Final.encryptCode v.1)
      verified := Proof.AesCfb.encryptFinal_keyed (Final.encryptFinal_framed v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.cfbEncryptFinalOwn v.1.encClear)
      Proof.Aes.AArch64.ModesScrub.cfbEncryptFinalOk (Proof.Aes.AArch64.ModesScrub.cfbEncryptFinalSide v.1 v.2)),
    Spec.Cfb.aesDecryptFinalApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Final.decryptCode v.1)
      verified := Proof.AesCfb.decryptFinal_keyed (Final.decryptFinal_framed v.1) } Proof.Aes.AArch64.ModesScrub.cfbDecryptFinalOk)]

end VG.Artifacts.AesCfb.AArch64
