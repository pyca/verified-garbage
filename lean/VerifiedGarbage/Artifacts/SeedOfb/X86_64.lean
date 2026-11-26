module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
import VerifiedGarbage.Impl.Seed.X86_64.Fn
import VerifiedGarbage.Proof.Seed.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-OFB on x86-64 -/

namespace VG.Artifacts.SeedOfb.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Seed.ofbApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ofb, verified := Proof.Seed.X86_64.Scrub.ofb_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ofb_spSafe },
  Spec.Seed.ofbFinalApi.artifact X86_64.target { code := Impl.Seed.X86_64.Fn.ofbFinal, verified := Proof.Seed.X86_64.Scrub.ofbFinal_scrubbed, spSafe := Proof.Seed.X86_64.Scrub.ofbFinal_spSafe }]

spec_apis artifacts

end VG.Artifacts.SeedOfb.X86_64
