module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit

/-! # SEED-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.cbcEncryptChainedReg,
  Spec.Seed.cbcDecryptChainedApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.SeedCbc.PPC64LE
