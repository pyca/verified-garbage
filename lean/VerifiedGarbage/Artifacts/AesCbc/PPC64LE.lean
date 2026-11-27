module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Wiped
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CBC (NIST SP 800-38A §6.2) on PPC64LE -/

namespace VG.Artifacts.AesCbc.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Cbc.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cbcEncrypt
    verified := Proof.Aes.PPC64LE.Scrub.cbcEncrypt_scrubbed
    publicOutOk := Proof.Aes.PPC64LE.Scrub.cbcEncrypt_public },
  Spec.Cbc.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.cbcDecrypt
    verified := Proof.Aes.PPC64LE.Scrub.cbcDecrypt_scrubbed
    publicOutOk := Proof.Aes.PPC64LE.Scrub.cbcDecrypt_public }]

spec_apis artifacts

end VG.Artifacts.AesCbc.PPC64LE
