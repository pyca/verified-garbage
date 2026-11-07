module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Caller
public import VerifiedGarbage.Proof.AesCfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.AesCfb.AArch64.Body

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCfb

open VG.Proof.AesCfb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCfb.AArch64.encrypt v.enc
    verified := Proof.AesCfb.encrypt_keyed (encrypt_verified v)
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Caller.decrypt v
    verified := Proof.AesCfb.decrypt_keyed (Caller.verified v)
    written := Caller.written v
    writtenOk := Caller.written_ok v
    features := v.features },
  Spec.Cfb.aesEncryptFinalApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Final.encryptCode v)
    stack := 64
    verified := Proof.AesCfb.encryptFinal_keyed (Final.encryptFinal_framed v)
    features := v.features },
  Spec.Cfb.aesDecryptFinalApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Final.decryptCode v)
    stack := 64
    verified := Proof.AesCfb.decryptFinal_keyed (Final.decryptFinal_framed v)
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCfb
