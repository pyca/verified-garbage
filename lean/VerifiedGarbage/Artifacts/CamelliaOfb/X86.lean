module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ofb
public import VerifiedGarbage.Spec.Camellia.OfbFinal
import VerifiedGarbage.Proof.Camellia.X86.SseScrub
import VerifiedGarbage.Impl.Camellia.X86.SseFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiScrub
import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-OFB on x86 -/

namespace VG.Artifacts.CamelliaOfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Camellia.ofbApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.ofb
    verified := Proof.Camellia.X86.AesNi.Scrub.ofb_scrubbed },
  Spec.Camellia.ofbApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.ofb
    verified := Proof.Camellia.X86.Sse.Scrub.ofb_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.ofbFinal
    verified := Proof.Camellia.X86.AesNi.Scrub.ofbFinal_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.ofbFinal
    verified := Proof.Camellia.X86.Sse.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaOfb.X86
