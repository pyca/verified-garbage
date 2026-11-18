module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cbcEncryptReg,
  Spec.Cbc.aesDecryptApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.cbcDecryptReg]

end VG.Artifacts.AesCbc.PPC64LE
