module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.AesEcb.Contract
import VerifiedGarbage.Proof.AesEcb.PPC64LE
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-ECB (NIST SP 800-38A §6.1) on PPC64LE -/

namespace VG.Artifacts.AesEcb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.AesEcb.encryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Aes.PPC64LE.Scrub.ecbEncrypt_scrubbed
    publicOutOk := Proof.Aes.PPC64LE.Scrub.ecbEncrypt_public },
  Spec.AesEcb.decryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Aes.PPC64LE.Scrub.ecbDecrypt_scrubbed
    publicOutOk := Proof.Aes.PPC64LE.Scrub.ecbDecrypt_public }]

spec_apis artifacts

end VG.Artifacts.AesEcb.PPC64LE
