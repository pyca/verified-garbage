module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Impl.AesCbc.AArch64.Fn
import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit
import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
import VerifiedGarbage.Proof.Variants.AesCbc.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CBC (NIST SP 800-38A §6.2) on AArch64 -/

namespace VG.Artifacts.AesCbc.AArch64

open VG.Proof.AesCbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes_sha3"
    code := Impl.AesCbc.AArch64.Fn.decrypt
    verified := Proof.AesCbc.AArch64.Decrypt.codeC_scrubbed
    publicOutOk := Proof.AesCbc.AArch64.Decrypt.codeC_public
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenC },
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Fn.decryptAes
    verified := Proof.AesCbc.AArch64.Decrypt.codeAesC_scrubbed
    publicOutOk := Proof.AesCbc.AArch64.Decrypt.codeAesC_public
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenAesC },
  Spec.Cbc.aesEncryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Fn.encryptAes
    verified := Proof.AesCbc.AArch64.Wiped.encryptAes_scrubbed
    publicOutOk := Proof.AesCbc.AArch64.Wiped.encryptAes_public
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Wiped.encryptAes_written }] ++
  (VG.Proof.Variants.AesCbc.AArch64.variants.flatMap fun (v : Wiped.CbcImpl) => [
    Spec.Cbc.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCbc.AArch64.Fn.encrypt v.suffix v.enc
      verified := Proof.AesCbc.AArch64.Wiped.encryptWiped_scrubbed v
      publicOutOk := Proof.AesCbc.AArch64.Wiped.encryptWiped_public v },
    Spec.Cbc.aesDecryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCbc.AArch64.Fn.decryptWiped v.suffix v.dec
      verified := Proof.AesCbc.AArch64.Wiped.decryptWiped_scrubbed v
      publicOutOk := Proof.AesCbc.AArch64.Wiped.decryptWiped_public v }])

spec_apis artifacts

end VG.Artifacts.AesCbc.AArch64
