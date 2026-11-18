module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Verified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Camellia on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Camellia.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.expandKeyReg,
  Spec.Camellia.ecbEncryptApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.ecbEncReg,
  Spec.Camellia.ecbDecryptApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.ecbDecReg]

end VG.Artifacts.Camellia.PPC64LE
