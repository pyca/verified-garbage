module

public import VerifiedGarbage.Proof.AesXts.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesXts.PPC64LE

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact PPC64LE.target Proof.AesXts.PPC64LE.Scrub.encryptUnitReg,
  Spec.Xts.aesDecryptUnitApi.artifact PPC64LE.target Proof.AesXts.PPC64LE.Scrub.decryptUnitReg]

end VG.Artifacts.AesXts.PPC64LE
