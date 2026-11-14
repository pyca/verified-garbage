module

public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit

/-! # SEED-CFB128 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86_64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.cfbEncryptReg,
  Spec.Seed.cfbDecryptApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.cfbDecryptReg,
  Spec.Seed.cfbEncryptFinalApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.cfbEncryptFinalReg,
  Spec.Seed.cfbDecryptFinalApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.SeedCfb.X86_64
