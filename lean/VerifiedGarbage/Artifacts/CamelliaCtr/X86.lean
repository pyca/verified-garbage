module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Camellia.X86.Scrub
import VerifiedGarbage.Impl.Camellia.X86.Fn
import VerifiedGarbage.Proof.Camellia.X86.SseScrub
import VerifiedGarbage.Impl.Camellia.X86.SseFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Variants.CamelliaCtr.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CTR on x86 -/

namespace VG.Artifacts.CamelliaCtr.X86

/-- `vg_camellia_ctr_final`, with each implementation of `vg_camellia_ctr`'s code. -/
def finals : List (Artifact X86.target) :=
  VG.Proof.Variants.CamelliaCtr.X86.variants.map fun (c : Proof.Camellia.X86.CtrFinal.CtrImpl) =>
    Spec.Camellia.ctrFinalApi.artifact X86.target {
      suffix := c.suffix
      code := Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words
      verified := Proof.Camellia.X86.Scrub.ctrFinal_scrubbed c
      spSafe := Proof.Camellia.X86.Scrub.ctrFinal_spSafeF c }

public def artifacts : List (Artifact X86.target) := [
  Spec.Camellia.ctrApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.ctr
    verified := Proof.Camellia.X86.AesNiWide.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.ctr
    verified := Proof.Camellia.X86.Sse.Scrub.ctr_scrubbed }] ++ finals

spec_apis artifacts

end VG.Artifacts.CamelliaCtr.X86
