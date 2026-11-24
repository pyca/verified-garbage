module

public import VerifiedGarbage.Proof.Seed.X86.SseScrub
public import VerifiedGarbage.Impl.Seed.X86.SseFn
public import VerifiedGarbage.Proof.Seed.X86.AesNiScrub
public import VerifiedGarbage.Impl.Seed.X86.AesNiFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiLit

/-! # SEED-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.SeedOfb.X86
