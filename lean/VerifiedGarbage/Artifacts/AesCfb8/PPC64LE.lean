module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on PPC64LE -/

namespace VG.Artifacts.AesCfb8.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cfb8.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfb8Encrypt
    verified := Proof.Aes.PPC64LE.Scrub.cfb8Encrypt_scrubbed },
  Spec.Cfb8.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cfb8Decrypt
    verified := Proof.Aes.PPC64LE.Scrub.cfb8Decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCfb8.PPC64LE
