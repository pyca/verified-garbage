module

public import VerifiedGarbage.Proof.AesEcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-ECB (NIST SP 800-38A §6.1) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesEcb.PPC64LE

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ecbEncrypt
    verified := Proof.Aes.PPC64LE.Scrub.ecbEncrypt_scrubbed },
  Spec.AesEcb.decryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.Fn.ecbDecrypt
    verified := Proof.Aes.PPC64LE.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.AesEcb.PPC64LE
