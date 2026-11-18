module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Blowfish on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Blowfish.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.expandKeyReg,
  Spec.Blowfish.ecbEncryptApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.ecbEncryptReg,
  Spec.Blowfish.ecbDecryptApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.ecbDecryptReg]

end VG.Artifacts.Blowfish.PPC64LE
