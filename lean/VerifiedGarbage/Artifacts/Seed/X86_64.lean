module

public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-! # SEED on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86_64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.expandKeyReg,
  Spec.Seed.ecbEncryptApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.ecbEncryptReg,
  Spec.Seed.ecbDecryptApi.artifact X86_64.target Proof.Seed.X86_64.Scrub.ecbDecryptReg]

end VG.Artifacts.Seed.X86_64
