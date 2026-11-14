module

public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit

/-! # SEED-CBC on x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86_64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.cbcEncryptReg,
  Spec.Seed.cbcDecryptChainedApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.cbcDecryptReg]

end VG.Artifacts.SeedCbc.X86_64
