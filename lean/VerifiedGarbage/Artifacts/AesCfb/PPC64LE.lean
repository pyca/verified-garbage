module

public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbEncrypt
    verified := .scrubbed Proof.Aes.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Cfb.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbDecrypt
    verified := .scrubbed Proof.Aes.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Cfb.aesEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Aes.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cfb.aesDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Aes.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.AesCfb.PPC64LE
