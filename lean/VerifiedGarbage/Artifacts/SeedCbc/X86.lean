module

public import VerifiedGarbage.Proof.Seed.X86.SseScrub
public import VerifiedGarbage.Impl.Seed.X86.SseFn
public import VerifiedGarbage.Proof.Seed.X86.AesNiScrub
public import VerifiedGarbage.Impl.Seed.X86.AesNiFn
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideScrub
public import VerifiedGarbage.Impl.Seed.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiLit
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit

/-! # SEED-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.SeedCbc.X86
