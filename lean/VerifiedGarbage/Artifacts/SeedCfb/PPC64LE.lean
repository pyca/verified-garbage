module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit

/-! # SEED-CFB128 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.cfbEncryptReg,
  Spec.Seed.cfbDecryptApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.cfbDecryptReg,
  Spec.Seed.cfbEncryptFinalApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.cfbEncryptFinalReg,
  Spec.Seed.cfbDecryptFinalApi.artifact PPC64LE.target Proof.Seed.PPC64LE.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.SeedCfb.PPC64LE
