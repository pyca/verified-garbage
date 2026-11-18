module

public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES (FIPS 197) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Aes.PPC64LE

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact PPC64LE.target Proof.Aes.PPC64LE.Scrub.expandKeyReg]

end VG.Artifacts.Aes.PPC64LE
