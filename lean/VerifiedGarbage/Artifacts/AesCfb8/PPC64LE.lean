module

public import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.PPC64LE

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cfb8EncryptReg,
  Spec.Cfb8.aesDecryptApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cfb8DecryptReg]

end VG.Artifacts.AesCfb8.PPC64LE
