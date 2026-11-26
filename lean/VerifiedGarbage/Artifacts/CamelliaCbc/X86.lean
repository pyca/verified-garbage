module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Camellia.X86.SseScrub
import VerifiedGarbage.Impl.Camellia.X86.SseFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiScrub
import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CBC on x86 -/

namespace VG.Artifacts.CamelliaCbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.cbcEncryptChained
    verified := Proof.Camellia.X86.AesNi.Scrub.cbcEncryptChained_scrubbed },
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.cbcEncryptChained
    verified := Proof.Camellia.X86.Sse.Scrub.cbcEncryptChained_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.cbcDecryptChained
    verified := Proof.Camellia.X86.AesNiWide.Scrub.cbcDecryptChained_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.cbcDecryptChained
    verified := Proof.Camellia.X86.Sse.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCbc.X86
