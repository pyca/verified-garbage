module

public import VerifiedGarbage.Impl.Seed.X86_64.Fn
public import VerifiedGarbage.Proof.Seed.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit

/-! # SEED-OFB on x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86_64

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ofb, verified := Proof.Seed.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ofb_spSafe },
  Spec.Seed.ofbFinalApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ofbFinal, verified := Proof.Seed.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ofbFinal_spSafe }]

end VG.Artifacts.SeedOfb.X86_64
