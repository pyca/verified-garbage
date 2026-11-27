module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
import VerifiedGarbage.Proof.Seed.X86.SseScrub
import VerifiedGarbage.Impl.Seed.X86.SseFn
import VerifiedGarbage.Proof.Seed.X86.AesNiScrub
import VerifiedGarbage.Impl.Seed.X86.AesNiFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-OFB on x86 -/

namespace VG.Artifacts.SeedOfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Seed.ofbApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.ofb
    verified := Proof.Seed.X86.AesNi.Scrub.ofb_scrubbed },
  Spec.Seed.ofbApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.ofb
    verified := Proof.Seed.X86.Sse.Scrub.ofb_scrubbed },
  Spec.Seed.ofbFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.ofbFinal
    verified := Proof.Seed.X86.AesNi.Scrub.ofbFinal_scrubbed },
  Spec.Seed.ofbFinalApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.ofbFinal
    verified := Proof.Seed.X86.Sse.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedOfb.X86
