module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.AesCfb.AArch64.Final
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCfb.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on AArch64 -/

namespace VG.Artifacts.AesCfb.AArch64

open VG.Proof.AesCfb.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesCfb.AArch64.variants.flatMap fun (v : CfbImpl) => [
    Spec.Cfb.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.encrypt v.enc
      verified := Proof.AesCfb.AArch64.Final.encrypt_scrubbed v.blocks },
    Spec.Cfb.aesDecryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.decrypt v.dec
      verified := Proof.AesCfb.AArch64.Final.decrypt_scrubbed v
      written := v.written
      writtenOk := Proof.AesCfb.AArch64.Final.decrypt_written v },
    Spec.Cfb.aesEncryptFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.encryptFinal v.enc v.suffix
      verified := Proof.AesCfb.AArch64.Final.encryptFinal_scrubbed v.blocks },
    Spec.Cfb.aesDecryptFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb.AArch64.Fn.decryptFinal v.enc v.suffix v.dec
      verified := Proof.AesCfb.AArch64.Final.decryptFinal_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.AesCfb.AArch64
