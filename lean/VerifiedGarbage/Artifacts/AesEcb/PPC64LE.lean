module

public import VerifiedGarbage.Proof.AesEcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-ECB (NIST SP 800-38A §6.1) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesEcb.PPC64LE

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.encryptBlocks
    verified := Proof.AesEcb.PPC64LE.encrypt_verified },
  Spec.AesEcb.decryptApi.artifact PPC64LE.target {
    code := Impl.Aes.PPC64LE.decryptBlocks
    verified := Proof.AesEcb.PPC64LE.decrypt_verified }]

end VG.Artifacts.AesEcb.PPC64LE
