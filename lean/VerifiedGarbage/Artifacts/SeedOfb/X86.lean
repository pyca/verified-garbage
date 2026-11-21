module

public import VerifiedGarbage.Proof.Seed.X86.Scrub
public import VerifiedGarbage.Impl.Seed.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.FbLit
import VerifiedGarbage.Proof.Seed.X86.FbFinalLit

/-! # SEED-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.ofb
    verified := Proof.Seed.X86.Scrub.ofb_scrubbed },
  Spec.Seed.ofbFinalApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.ofbFinal
    verified := Proof.Seed.X86.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.SeedOfb.X86
