module

public import VerifiedGarbage.Proof.Camellia.X86.SseScrub
public import VerifiedGarbage.Impl.Camellia.X86.SseFn
public import VerifiedGarbage.Proof.Camellia.X86.AesNiScrub
public import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiLit

/-! # Camellia-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.CamelliaOfb.X86
