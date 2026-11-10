module

public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit

/-! # SEED-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86_64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.ofbReg,
  Spec.Seed.ofbFinalApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.ofbFinalReg]

end VG.Artifacts.SeedOfb.X86_64
