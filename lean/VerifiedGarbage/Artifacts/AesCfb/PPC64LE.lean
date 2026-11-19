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
  Spec.Cfb.aesEncryptApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cfbEncryptReg,
  Spec.Cfb.aesDecryptApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cfbDecryptReg,
  Spec.Cfb.aesEncryptFinalApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.Cfb.aesDecryptFinalApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.AesCfb.PPC64LE
