module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on PPC64LE -/

namespace VG.Artifacts.AesCfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cfb.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Aes.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Cfb.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Aes.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Cfb.aesEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Aes.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cfb.aesDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Aes.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCfb.PPC64LE
