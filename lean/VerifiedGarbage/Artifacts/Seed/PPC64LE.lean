module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit

/-! # SEED on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Seed.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.expandKeyReg,
  Spec.Seed.ecbEncryptApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.ecbEncryptReg,
  Spec.Seed.ecbDecryptApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.ecbDecryptReg]

end VG.Artifacts.Seed.PPC64LE
