module

public import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit

/-! # SEED-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86_64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofb
    stack := 1552
    verified := Proof.Seed.X86_64.ofb_framed }]

end VG.Artifacts.SeedOfb.X86_64
