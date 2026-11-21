module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Fn
public import VerifiedGarbage.Proof.AesCbc.AArch64.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit
public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.Variants.AesCbc.AArch64

/-! # AES-CBC (NIST SP 800-38A §6.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.AArch64

open VG.Proof.AesCbc.AArch64

def artifacts : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes_sha3"
    code := Impl.AesCbc.AArch64.Fn.decrypt
    verified := Proof.AesCbc.AArch64.Decrypt.codeC_scrubbed
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenC },
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Fn.decryptAes
    verified := Proof.AesCbc.AArch64.Decrypt.codeAesC_scrubbed
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.writtenAesC },
  Spec.Cbc.aesEncryptApi.artifact VG.AArch64.target {
    suffix := "_aes"
    code := Impl.AesCbc.AArch64.Fn.encryptAes
    verified := Wiped.encryptAes_scrubbed
    written := [("scratch",0)]
    writtenOk := Wiped.encryptAes_written }] ++
  (VG.Proof.Variants.AesCbc.AArch64.variants.flatMap fun (v : Wiped.CbcImpl) => [
    Spec.Cbc.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCbc.AArch64.Fn.encrypt v.suffix v.enc
      verified := Wiped.encryptWiped_scrubbed v },
    Spec.Cbc.aesDecryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCbc.AArch64.Fn.decryptWiped v.suffix v.dec
      verified := Wiped.decryptWiped_scrubbed v }])

end VG.Artifacts.AesCbc.AArch64
