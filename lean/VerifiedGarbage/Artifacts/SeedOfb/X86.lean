module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.FbLit

/-! # SEED-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.ofb
    stack := 1188
    verified := Proof.Seed.X86.Fb.ofb_framed }]

end VG.Artifacts.SeedOfb.X86
