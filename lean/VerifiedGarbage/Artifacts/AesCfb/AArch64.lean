module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesCfb.AArch64

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.AArch64

open VG.Proof.AesCfb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCfb.AArch64.variants.flatMap fun (v : CfbImpl) => [
    Spec.Cfb.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.encrypt v.enc
      verified := .scrubbed (Final.encrypt_scrubbed v.blocks) },
    Spec.Cfb.aesDecryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.decrypt v.dec
      verified := .scrubbed (Final.decrypt_scrubbed v)
      written := v.written
      writtenOk := Final.decrypt_written v },
    Spec.Cfb.aesEncryptFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.encryptFinal v.enc v.suffix
      verified := .scrubbed (Final.encryptFinal_scrubbed v.blocks) },
    Spec.Cfb.aesDecryptFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.decryptFinal v.enc v.suffix v.dec
      verified := .scrubbed (Final.decryptFinal_scrubbed v) }]

end VG.Artifacts.AesCfb.AArch64
