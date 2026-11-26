module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Proof.Seed.X86.SseScrub
import VerifiedGarbage.Impl.Seed.X86.SseFn
import VerifiedGarbage.Proof.Seed.X86.AesNiScrub
import VerifiedGarbage.Impl.Seed.X86.AesNiFn
import VerifiedGarbage.Proof.Seed.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Seed.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiLit
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CBC on x86 -/

namespace VG.Artifacts.SeedCbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cbcEncryptChained
    verified := Proof.Seed.X86.AesNi.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.cbcEncryptChained
    verified := Proof.Seed.X86.Sse.Scrub.cbcEncryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNiWide.Fn.cbcDecryptChained
    verified := Proof.Seed.X86.AesNiWide.Scrub.cbcDecryptChained_scrubbed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.cbcDecryptChained
    verified := Proof.Seed.X86.Sse.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCbc.X86
