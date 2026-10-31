module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) of whole blocks on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesXts.AArch64

open VG.Proof.AesXts.AArch64

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact AArch64.target {
    code := (XtsImpl.blocks .scalar).enc.code
    verified := encrypt_verified .scalar },
  Spec.Xts.aesDecryptApi.artifact AArch64.target {
    code := (XtsImpl.blocks .scalar).dec.code
    verified := decrypt_verified .scalar },
  Spec.Xts.aesEncryptApi.artifact AArch64.target {
    suffix := "_aes"
    code := Impl.AesXts.AArch64Aes.encrypt
    verified := Aes.encrypt_verified
    features := ["aes"] },
  Spec.Xts.aesDecryptApi.artifact AArch64.target {
    suffix := "_aes"
    code := Impl.AesXts.AArch64Aes.decrypt
    verified := Aes.decrypt_verified
    features := ["aes"] }]

end VG.Artifacts.AesXts.AArch64
